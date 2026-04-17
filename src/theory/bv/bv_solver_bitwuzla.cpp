/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-blasting solver that supports multiple SAT backends.
 */

#include "theory/bv/bv_solver_bitwuzla.h"

#include <bitwuzla/cpp/bitwuzla.h>

#include "options/bv_options.h"
#include "prop/sat_solver_factory.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * Terminator for bitwuzla that forwards cvc5's resource limit checks.
 *
 * Bitwuzla polls terminate() periodically inside check_sat(). Returning true
 * causes bitwuzla to abort the current check and return UNKNOWN, which cvc5
 * then maps to a timeout/resource-out result — the same mechanism used by the
 * CaDiCaL integration.
 *
 * The terminator is reconnected on each initSatSolver() call (including after
 * a reset-assertions). The bitwuzla push/pop stack tracked by d_bitwuzlaLevel
 * and BitwuzlaContextNotify is not affected: push/pop operations occur before
 * check_sat(), so the stack level is always consistent when a timeout fires.
 */
class BitwuzlaTerminator : public bitwuzla::Terminator
{
 public:
  BitwuzlaTerminator(ResourceManager& resmgr) : d_resmgr(resmgr) {}
  bool terminate() override { return d_resmgr.out(); }

 private:
  ResourceManager& d_resmgr;
};

/**
 * Notifies the BV solver when the SAT context is popped.
 *
 * Used to mirror cvc5's SAT context with bitwuzla's push()/pop() interface so
 * that learned clauses accumulate correctly across incremental calls.
 */
class BitwuzlaContextNotify : public context::ContextNotifyObj
{
 public:
  BitwuzlaContextNotify(context::Context* c, BVSolverBitwuzla* solver)
      : context::ContextNotifyObj(c, false), d_solver(solver)
  {
  }

 protected:
  void contextNotifyPop() override { d_solver->notifyContextPop(); }

 private:
  BVSolverBitwuzla* d_solver;
};

/**
 * Notifies the BV solver when assertions were reset.
 *
 * This class is notified after every user-context pop and maintains a flag
 * that indicates whether assertions have been reset. If the user-context level
 * reaches level 0 it means that the assertions were reset.
 */
class NotifyResetAssertions : public context::ContextNotifyObj
{
 public:
  NotifyResetAssertions(context::Context* c)
      : context::ContextNotifyObj(c, false),
        d_context(c),
        d_doneResetAssertions(false)
  {
  }

  bool doneResetAssertions() { return d_doneResetAssertions; }

  void reset() { d_doneResetAssertions = false; }

 protected:
  void contextNotifyPop() override
  {
    // If the user-context level reaches 0 it means that reset-assertions was
    // called.
    if (d_context->getLevel() == 0)
    {
      d_doneResetAssertions = true;
    }
  }

 private:
  /** The user-context. */
  context::Context* d_context;

  /** Flag to notify whether reset assertions was called. */
  bool d_doneResetAssertions;
};

BVSolverBitwuzla::BVSolverBitwuzla(Env& env,
                                   TheoryState* s,
                                   TheoryInferenceManager& inferMgr)
    : BVSolver(env, *s, inferMgr),
      d_bbFacts(context()),
      d_bbInputFacts(context()),
      d_assertions(context()),
      d_factLiteralCache(context()),
      d_literalFactCache(context()),
      d_propagate(options().bv.bitvectorPropagate),
      d_resetNotify(new NotifyResetAssertions(userContext())),
      d_satContextNotify(new BitwuzlaContextNotify(context(), this)),
      d_bitwuzlaLevel(0)
{
  initSatSolver();
}

bool BVSolverBitwuzla::needsEqualityEngine(EeSetupInfo& esi)
{
  // we always need the equality engine if sharing is enabled for processing
  // equality engine and shared terms
  return logicInfo().isSharingEnabled() || options().bv.bvEqEngine;
}

void BVSolverBitwuzla::postCheck(Theory::Effort level)
{
  // Count calls at each effort level for diagnostic purposes.
  static uint64_t s_calls_full = 0, s_calls_other = 0;
  if (level != Theory::Effort::EFFORT_FULL)
  {
    ++s_calls_other;
    Trace("bv-bitwuzla-check")
        << "BVSolverBitwuzla::postCheck non-FULL (other=" << s_calls_other
        << " full=" << s_calls_full << ")" << std::endl;
    /* No propagation support: skip check_sat at non-FULL effort levels. */
    return;
  }
  ++s_calls_full;
  Trace("bv-bitwuzla-check")
      << "BVSolverBitwuzla::postCheck FULL (other=" << s_calls_other
      << " full=" << s_calls_full << ")" << std::endl;

  // If assertions were fully reset, reinitialize bitwuzla from scratch.
  if (d_resetNotify->doneResetAssertions())
  {
    d_bitwuzla.reset(nullptr);
    initSatSolver();
    d_resetNotify->reset();
  }

  // Mirror the cvc5 SAT context level with bitwuzla push()/pop().
  // Pop notifications are handled by BitwuzlaContextNotify; here we push
  // when the context has moved deeper since the last postCheck.
  uint32_t ctxLevel = static_cast<uint32_t>(context()->getLevel());
  if (ctxLevel > d_bitwuzlaLevel)
  {
    d_bitwuzla->push(ctxLevel - d_bitwuzlaLevel);
    d_bitwuzlaLevel = ctxLevel;
  }

  /* Process input assertions bit-blast queue. */
  while (!d_bbInputFacts.empty())
  {
    Node fact = d_bbInputFacts.front();
    d_bbInputFacts.pop();
    if (d_factLiteralCache.find(fact) == d_factLiteralCache.end())
    {
      auto translated = translate(fact);
      d_bitwuzla->assert_formula(translated);
      d_assertions.push_back(fact);
      d_literalFactCache[translated] = fact;
      d_factLiteralCache[fact] = translated;
    }
  }

  /* Process bit-blast queue and permanently assert into bitwuzla. */
  while (!d_bbFacts.empty())
  {
    Node fact = d_bbFacts.front();
    d_bbFacts.pop();
    if (d_factLiteralCache.find(fact) == d_factLiteralCache.end())
    {
      auto translated = translate(fact);
      d_bitwuzla->assert_formula(translated);
      // Track in d_assertions so the fallback conflict path is always sound.
      d_assertions.push_back(fact);
      d_literalFactCache[translated] = fact;
      d_factLiteralCache[fact] = translated;
    }
  }

  bitwuzla::Result res = d_bitwuzla->check_sat();

  if (res == bitwuzla::Result::UNSAT)
  {
    auto nm = d_env.getNodeManager();
    // get_unsat_core() returns the subset of assert_formula() calls that
    // are jointly unsatisfiable.
    auto unsat_core = d_bitwuzla->get_unsat_core();

    std::vector<Node> conf;
    for (const auto& term : unsat_core)
    {
      auto it = d_literalFactCache.find(term);
      if (it != d_literalFactCache.end())
      {
        conf.push_back(it->second);
      }
    }
    if (conf.empty())
    {
      // Fallback: blame all current input assertions.
      conf.assign(d_assertions.begin(), d_assertions.end());
    }
    Node conflict = nm->mkAnd(conf);
    d_im.conflict(conflict, InferenceId::BV_BITBLAST_CONFLICT);
  }
}

bool BVSolverBitwuzla::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Valuation& val = d_state.getValuation();

  /**
   * Check whether `fact` is an input assertion on user-level 0.
   *
   * If this is the case we can assert `fact` to the SAT solver instead of
   * using assumptions.
   */
  if (options().bv.bvAssertInput && val.isFixed(fact))
  {
    Assert(!val.isDecision(fact));
    d_bbInputFacts.push_back(fact);
  }
  else
  {
    d_bbFacts.push_back(fact);
  }

  // Return false to enable equality engine reasoning in Theory, which is
  // available if we are using the equality engine.
  return !logicInfo().isSharingEnabled() && !options().bv.bvEqEngine;
}

TrustNode BVSolverBitwuzla::explain(TNode n)
{
  Trace("bv-bitblast") << "explain called on " << n << std::endl;
  return d_im.explainLit(n);
}

void BVSolverBitwuzla::computeRelevantTerms(std::set<Node>& termSet)
{
  /* BITVECTOR_EAGER_ATOM wraps input assertions that may also contain
   * equalities. As a result, these equalities are not handled by the equality
   * engine and terms below these equalities do not appear in `termSet`.
   * We need to make sure that we compute model values for all relevant terms
   * in BitblastMode::EAGER and therefore add all variables from the
   * bit-blaster to `termSet`.
   */
  // if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  //{
  //   d_bitblaster->computeRelevantTerms(termSet);
  // }
  //  TODO:
  // Assert(false);
}

bool BVSolverBitwuzla::collectModelValues(TheoryModel* m,
                                          const std::set<Node>& termSet)
{
  for (const auto& term : termSet)
  {
    // Only collect model values for BV and Boolean terms. Non-BV/non-Bool
    // terms (e.g., FP) are translated to opaque Bool placeholders and must
    // not be given a Bool model value — the model would reject the type
    // mismatch and return false, causing d_modelBuiltSuccess to be false.
    if (!term.getType().isBitVector() && !term.getType().isBoolean())
    {
      continue;
    }

    auto it = d_translation_cache.find(term);
    if (it == d_translation_cache.end() || !it->second.is_const())
    {
      continue;
    }

    Node value = getValue(term, true);
    Assert(value.isConst());
    if (!m->assertEquality(term, value, true))
    {
      return false;
    }
  }
  /**/
  /*// In eager bitblast mode we also have to collect the model values for*/
  /*// Boolean variables in the CNF stream.*/
  /*if (options().bv.bitblastMode == options::BitblastMode::EAGER)*/
  /*{*/
  /*  NodeManager* nm = nodeManager();*/
  /*  std::vector<TNode> vars;*/
  /*  d_cnfStream->getBooleanVariables(vars);*/
  /*  for (TNode var : vars)*/
  /*  {*/
  /*    Assert(d_cnfStream->hasLiteral(var));*/
  /*    prop::SatLiteral bit = d_cnfStream->getLiteral(var);*/
  /*    prop::SatValue value = d_satSolver->modelValue(bit);*/
  /*    Assert(value != prop::SAT_VALUE_UNKNOWN);*/
  /*    if (!m->assertEquality(*/
  /*            var, nm->mkConst(value == prop::SAT_VALUE_TRUE), true))*/
  /*    {*/
  /*      return false;*/
  /*    }*/
  /*  }*/
  /*}*/
  /**/
  return true;
}

void BVSolverBitwuzla::initSatSolver()
{
  d_bitwuzlaLevel = 0;
  bitwuzla::Options opts;
  opts.set(bitwuzla::Option::PRODUCE_UNSAT_CORES, true);
  opts.set(bitwuzla::Option::PRODUCE_MODELS, true);
  d_bitwuzla.reset(new bitwuzla::Bitwuzla(d_bitwuzla_tm, opts));
  d_terminator.reset(new BitwuzlaTerminator(*resourceManager()));
  d_bitwuzla->configure_terminator(d_terminator.get());
}

void BVSolverBitwuzla::notifyContextPop()
{
  if (d_bitwuzlaLevel > 0)
  {
    d_bitwuzla->pop(1);
    --d_bitwuzlaLevel;
  }
}

namespace {
std::unordered_map<Kind, bitwuzla::Kind> kindmap = {
    {Kind::NOT, bitwuzla::Kind::NOT},
    {Kind::AND, bitwuzla::Kind::AND},
    {Kind::OR, bitwuzla::Kind::OR},
    {Kind::XOR, bitwuzla::Kind::XOR},
    {Kind::IMPLIES, bitwuzla::Kind::IMPLIES},
    {Kind::EQUAL, bitwuzla::Kind::EQUAL},
    {Kind::ITE, bitwuzla::Kind::ITE},
    {Kind::BITVECTOR_ULT, bitwuzla::Kind::BV_ULT},
    {Kind::BITVECTOR_ULE, bitwuzla::Kind::BV_ULE},
    {Kind::BITVECTOR_UGT, bitwuzla::Kind::BV_UGT},
    {Kind::BITVECTOR_UGE, bitwuzla::Kind::BV_UGE},
    {Kind::BITVECTOR_SLT, bitwuzla::Kind::BV_SLT},
    {Kind::BITVECTOR_SLE, bitwuzla::Kind::BV_SLE},
    {Kind::BITVECTOR_SGT, bitwuzla::Kind::BV_SGT},
    {Kind::BITVECTOR_SGE, bitwuzla::Kind::BV_SGE},
    {Kind::BITVECTOR_NOT, bitwuzla::Kind::BV_NOT},
    {Kind::BITVECTOR_CONCAT, bitwuzla::Kind::BV_CONCAT},
    {Kind::BITVECTOR_AND, bitwuzla::Kind::BV_AND},
    {Kind::BITVECTOR_OR, bitwuzla::Kind::BV_OR},
    {Kind::BITVECTOR_XOR, bitwuzla::Kind::BV_XOR},
    {Kind::BITVECTOR_XNOR, bitwuzla::Kind::BV_XNOR},
    {Kind::BITVECTOR_NAND, bitwuzla::Kind::BV_NAND},
    {Kind::BITVECTOR_NOR, bitwuzla::Kind::BV_NOR},
    {Kind::BITVECTOR_COMP, bitwuzla::Kind::BV_COMP},
    {Kind::BITVECTOR_MULT, bitwuzla::Kind::BV_MUL},
    {Kind::BITVECTOR_ADD, bitwuzla::Kind::BV_ADD},
    {Kind::BITVECTOR_SUB, bitwuzla::Kind::BV_SUB},
    {Kind::BITVECTOR_NEG, bitwuzla::Kind::BV_NEG},
    {Kind::BITVECTOR_UDIV, bitwuzla::Kind::BV_UDIV},
    {Kind::BITVECTOR_UREM, bitwuzla::Kind::BV_UREM},
    {Kind::BITVECTOR_SHL, bitwuzla::Kind::BV_SHL},
    {Kind::BITVECTOR_LSHR, bitwuzla::Kind::BV_SHR},
    {Kind::BITVECTOR_ASHR, bitwuzla::Kind::BV_ASHR},
    {Kind::BITVECTOR_EXTRACT, bitwuzla::Kind::BV_EXTRACT},
    {Kind::BITVECTOR_REPEAT, bitwuzla::Kind::BV_REPEAT},
    {Kind::BITVECTOR_ZERO_EXTEND, bitwuzla::Kind::BV_ZERO_EXTEND},
    {Kind::BITVECTOR_SIGN_EXTEND, bitwuzla::Kind::BV_SIGN_EXTEND},
    {Kind::BITVECTOR_ROTATE_RIGHT, bitwuzla::Kind::BV_ROR},
    {Kind::BITVECTOR_ROTATE_LEFT, bitwuzla::Kind::BV_ROL},
    // Signed arithmetic
    {Kind::BITVECTOR_SDIV, bitwuzla::Kind::BV_SDIV},
    {Kind::BITVECTOR_SREM, bitwuzla::Kind::BV_SREM},
    {Kind::BITVECTOR_SMOD, bitwuzla::Kind::BV_SMOD},
    // Reduction operators
    {Kind::BITVECTOR_REDAND, bitwuzla::Kind::BV_REDAND},
    {Kind::BITVECTOR_REDOR, bitwuzla::Kind::BV_REDOR},
    // Overflow detection
    {Kind::BITVECTOR_NEGO, bitwuzla::Kind::BV_NEG_OVERFLOW},
    {Kind::BITVECTOR_SADDO, bitwuzla::Kind::BV_SADD_OVERFLOW},
    {Kind::BITVECTOR_UADDO, bitwuzla::Kind::BV_UADD_OVERFLOW},
    {Kind::BITVECTOR_SMULO, bitwuzla::Kind::BV_SMUL_OVERFLOW},
    {Kind::BITVECTOR_UMULO, bitwuzla::Kind::BV_UMUL_OVERFLOW},
    {Kind::BITVECTOR_SSUBO, bitwuzla::Kind::BV_SSUB_OVERFLOW},
    {Kind::BITVECTOR_USUBO, bitwuzla::Kind::BV_USUB_OVERFLOW},
    {Kind::BITVECTOR_SDIVO, bitwuzla::Kind::BV_SDIV_OVERFLOW}};
}

const bitwuzla::Term& BVSolverBitwuzla::translate(const Node& n)
{
  std::vector<TNode> visit;
  if (n.getKind() == Kind::BITVECTOR_EAGER_ATOM)
  {
    visit.push_back(n[0]);
  }
  else
  {
    visit.push_back(n);
  }
  do
  {
    TNode cur = visit.back();

    auto [it, inserted] = d_translation_cache.emplace(cur, bitwuzla::Term());
    if (inserted)
    {
      if (cur.getKind() != Kind::APPLY_SELECTOR)
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    else if (it->second.is_null())
    {
      auto k = cur.getKind();

      bitwuzla::Term translated;
      if (k == Kind::CONST_BITVECTOR)
      {
        uint64_t size = utils::getSize(cur);
        bitwuzla::Sort bvsort = d_bitwuzla_tm.mk_bv_sort(size);
        const BitVector& bv = cur.getConst<BitVector>();
        std::string value = bv.toString(2);
        translated = d_bitwuzla_tm.mk_bv_value(bvsort, value, 2);
      }
      else if (kindmap.find(k) != kindmap.end())
      {
        std::vector<bitwuzla::Term> children;
        for (const auto& c : cur)
        {
          auto iit = d_translation_cache.find(c);
          Assert(iit != d_translation_cache.end());
          children.push_back(iit->second);
        }

        std::vector<uint64_t> indices;
        if (cur.getKind() == Kind::BITVECTOR_EXTRACT)
        {
          indices.push_back(utils::getExtractHigh(cur));
          indices.push_back(utils::getExtractLow(cur));
        }
        else if (cur.getKind() == Kind::BITVECTOR_SIGN_EXTEND)
        {
          indices.push_back(utils::getSignExtendAmount(cur));
        }
        else if (cur.getKind() == Kind::BITVECTOR_ZERO_EXTEND)
        {
          indices.push_back(utils::getZeroExtendAmount(cur));
        }
        else if (cur.getKind() == Kind::BITVECTOR_ROTATE_LEFT)
        {
          indices.push_back(utils::getRotateLeftAmount(cur));
        }
        else if (cur.getKind() == Kind::BITVECTOR_ROTATE_RIGHT)
        {
          indices.push_back(utils::getRotateRightAmount(cur));
        }
        else if (cur.getKind() == Kind::BITVECTOR_REPEAT)
        {
          indices.push_back(
              cur.getOperator().getConst<BitVectorRepeat>().d_repeatAmount);
        }

        translated = d_bitwuzla_tm.mk_term(kindmap[k], children, indices);
      }
      else if (k == Kind::BITVECTOR_ULTBV)
      {
        // BITVECTOR_ULTBV returns BV<1>; encode as ITE(ULT(a,b), bv1, bv0)
        auto iit0 = d_translation_cache.find(cur[0]);
        auto iit1 = d_translation_cache.find(cur[1]);
        Assert(iit0 != d_translation_cache.end());
        Assert(iit1 != d_translation_cache.end());
        bitwuzla::Sort s1 = d_bitwuzla_tm.mk_bv_sort(1);
        auto cmp = d_bitwuzla_tm.mk_term(
            bitwuzla::Kind::BV_ULT, {iit0->second, iit1->second});
        translated = d_bitwuzla_tm.mk_term(bitwuzla::Kind::ITE,
                                           {cmp,
                                            d_bitwuzla_tm.mk_bv_one(s1),
                                            d_bitwuzla_tm.mk_bv_zero(s1)});
      }
      else if (k == Kind::BITVECTOR_SLTBV)
      {
        // BITVECTOR_SLTBV returns BV<1>; encode as ITE(SLT(a,b), bv1, bv0)
        auto iit0 = d_translation_cache.find(cur[0]);
        auto iit1 = d_translation_cache.find(cur[1]);
        Assert(iit0 != d_translation_cache.end());
        Assert(iit1 != d_translation_cache.end());
        bitwuzla::Sort s1 = d_bitwuzla_tm.mk_bv_sort(1);
        auto cmp = d_bitwuzla_tm.mk_term(
            bitwuzla::Kind::BV_SLT, {iit0->second, iit1->second});
        translated = d_bitwuzla_tm.mk_term(bitwuzla::Kind::ITE,
                                           {cmp,
                                            d_bitwuzla_tm.mk_bv_one(s1),
                                            d_bitwuzla_tm.mk_bv_zero(s1)});
      }
      else if (k == Kind::BITVECTOR_ITE)
      {
        // BITVECTOR_ITE(cond:BV<1>, a, b); convert BV<1> cond to Bool
        auto iit0 = d_translation_cache.find(cur[0]);
        auto iit1 = d_translation_cache.find(cur[1]);
        auto iit2 = d_translation_cache.find(cur[2]);
        Assert(iit0 != d_translation_cache.end());
        Assert(iit1 != d_translation_cache.end());
        Assert(iit2 != d_translation_cache.end());
        bitwuzla::Sort s1 = d_bitwuzla_tm.mk_bv_sort(1);
        auto bool_cond = d_bitwuzla_tm.mk_term(
            bitwuzla::Kind::EQUAL,
            {iit0->second, d_bitwuzla_tm.mk_bv_one(s1)});
        translated = d_bitwuzla_tm.mk_term(
            bitwuzla::Kind::ITE, {bool_cond, iit1->second, iit2->second});
      }
      else
      {
        bitwuzla::Sort sort;
        if (cur.getType().isBoolean())
        {
          sort = d_bitwuzla_tm.mk_bool_sort();
        }
        else if (cur.getType().isBitVector())
        {
          uint64_t size = utils::getSize(cur);
          sort = d_bitwuzla_tm.mk_bv_sort(size);
        }
        else
        {
          // Non-BV, non-Boolean type (e.g., FP, Int, Real): treat as an
          // opaque Boolean constant. These nodes appear as shared terms from
          // other theories when (set-logic ALL) is in use; the BV solver does
          // not reason about them, so a fresh Bool placeholder is harmless.
          sort = d_bitwuzla_tm.mk_bool_sort();
        }
        translated = d_bitwuzla_tm.mk_const(sort);
      }
      it->second = translated;
    }
    visit.pop_back();
  } while (!visit.empty());

  if (n.getKind() == Kind::BITVECTOR_EAGER_ATOM)
  {
    auto it = d_translation_cache.find(n[0]);
    Assert(it != d_translation_cache.end());
    return it->second;
  }
  auto it = d_translation_cache.find(n);
  Assert(it != d_translation_cache.end());
  return it->second;
}

Node BVSolverBitwuzla::getValue(TNode node, bool initialize)
{
  if (node.isConst())
  {
    return node;
  }
  auto it = d_translation_cache.find(node);
  if (it == d_translation_cache.end())
  {
    // Node was never translated (e.g., a SyGuS synthesis sub-term that the BV
    // solver never bit-blasted). Mirror the BVSolverBitblast convention:
    // return null when !initialize, or a zero constant when initialize=true.
    if (!initialize)
    {
      return Node();
    }
    if (node.getType().isBitVector())
    {
      return utils::mkConst(nodeManager(), utils::getSize(node), 0u);
    }
    return utils::mkConst(nodeManager(), false);
  }
  auto val = d_bitwuzla->get_value(it->second);
  if (node.getType().isBitVector())
  {
    auto binval = val.value<std::string>(2);
    return utils::mkConst(nodeManager(), BitVector(binval));
  }
  else
  {
    Assert(node.getType().isBoolean());
    return utils::mkConst(nodeManager(), val.value<bool>());
  }
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
