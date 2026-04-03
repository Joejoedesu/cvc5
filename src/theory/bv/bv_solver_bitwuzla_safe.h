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
 * Bit-blasting solver backed by Bitwuzla — safe/conservative variant.
 *
 * Uses check_sat(assumptions) rather than push()/pop() + assert_formula().
 * No learned-clause reuse, but no stale-fact soundness risk either.
 *
 * See bv_solver_bitwuzla.h for the push/pop variant.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SOLVER_BITWUZLA_SAFE_H
#define CVC5__THEORY__BV__BV_SOLVER_BITWUZLA_SAFE_H

#include <bitwuzla/cpp/bitwuzla.h>

#include <unordered_map>

#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "proof/eager_proof_generator.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "smt/env_obj.h"
#include "theory/bv/bitblast/node_bitblaster.h"
#include "theory/bv/bv_solver.h"
#include "theory/bv/proof_checker.h"

namespace cvc5::internal {

namespace theory {
namespace bv {

class NotifyResetAssertionsSafe;

/**
 * Bit-blasting solver backed by Bitwuzla — safe/conservative variant.
 *
 * Differences from BVSolverBitwuzla (the push/pop variant):
 *  - Regular facts are passed as assumptions to check_sat() rather than being
 *    permanently asserted via assert_formula().
 *  - No push()/pop() mirroring of the cvc5 SAT context, so no dependency on
 *    ContextNotifyObj firing correctly.
 *  - Conflicts are extracted via get_unsat_assumptions() instead of
 *    get_unsat_core().
 *  - No learned-clause reuse across incremental check_sat() calls.
 */
class BVSolverBitwuzlaSafe : public BVSolver
{
 public:
  BVSolverBitwuzlaSafe(Env& env,
                       TheoryState* state,
                       TheoryInferenceManager& inferMgr);
  ~BVSolverBitwuzlaSafe() = default;

  bool needsEqualityEngine(EeSetupInfo& esi) override;

  void preRegisterTerm(TNode n) override {}

  void postCheck(Theory::Effort level) override;

  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  TrustNode explain(TNode n) override;

  std::string identify() const override { return "BVSolverBitwuzlaSafe"; };

  void computeRelevantTerms(std::set<Node>& termSet) override;

  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  /**
   * Get the current value of `node`.
   *
   * The `initialize` flag indicates whether bits should be zero-initialized
   * if they were not bit-blasted yet.
   */
  Node getValue(TNode node, bool initialize) override;

 private:
  /** Initialize the Bitwuzla instance with PRODUCE_UNSAT_ASSUMPTIONS. */
  void initSatSolver();

  const bitwuzla::Term& translate(const Node& n);

  /** Bitwuzla term manager and solver instance. */
  bitwuzla::TermManager d_bitwuzla_tm;
  std::unique_ptr<bitwuzla::Bitwuzla> d_bitwuzla;
  std::unordered_map<Node, bitwuzla::Term> d_translation_cache;

  /**
   * Bit-blast queue for facts sent to this solver.
   *
   * Gets populated on preNotifyFact().
   */
  context::CDQueue<Node> d_bbFacts;

  /**
   * Bit-blast queue for user-level 0 input facts sent to this solver.
   *
   * Get populated on preNotifyFact().
   */
  context::CDQueue<Node> d_bbInputFacts;

  /** Stores the current input assertions (permanently asserted, level-0). */
  context::CDList<Node> d_assertions;

  /**
   * Accumulates ALL currently-active regular (non-input) facts.
   *
   * Facts are appended here when first drained from d_bbFacts. Because this
   * is a CDList, entries added at context level L are automatically removed
   * when the context pops back past L, keeping this in sync with what the
   * equality engine and the SAT solver consider active.
   *
   * On every check_sat() call we pass the full contents of this list as
   * assumptions, ensuring bitwuzla sees all active facts even when multiple
   * postCheck(FULL) rounds occur at the same context level.
   */
  context::CDList<Node> d_regularFacts;

  /** Stores the bitwuzla::Term for a given fact. */
  context::CDHashMap<Node, bitwuzla::Term> d_factLiteralCache;

  /** Reverse map of `d_factLiteralCache`. */
  context::CDHashMap<bitwuzla::Term, Node> d_literalFactCache;

  /** Option to enable/disable bit-level propagation. */
  bool d_propagate;

  /** Notifies when reset-assertion was called. */
  std::unique_ptr<NotifyResetAssertionsSafe> d_resetNotify;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
