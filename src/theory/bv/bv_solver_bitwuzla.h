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
 * Bit-blasting solver that supports multiple SAT back ends.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SOLVER_BITWUZLA_H
#define CVC5__THEORY__BV__BV_SOLVER_BITWUZLA_H

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

class NotifyResetAssertions;
class BitwuzlaContextNotify;

/**
 * Bit-blasting solver with support for different SAT back ends.
 */
class BVSolverBitwuzla : public BVSolver
{
 public:
  BVSolverBitwuzla(Env& env,
                   TheoryState* state,
                   TheoryInferenceManager& inferMgr);
  ~BVSolverBitwuzla() = default;

  bool needsEqualityEngine(EeSetupInfo& esi) override;

  void preRegisterTerm(TNode n) override {}

  void postCheck(Theory::Effort level) override;

  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  TrustNode explain(TNode n) override;

  std::string identify() const override { return "BVSolverBitblast"; };

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
  friend class BitwuzlaContextNotify;

  /** Initialize SAT solver and CNF stream.  */
  void initSatSolver();

  const bitwuzla::Term& translate(const Node& n);

  /**
   * Called by BitwuzlaContextNotify when the SAT context is popped.
   * Mirrors the pop in bitwuzla so learned clauses are maintained correctly.
   */
  void notifyContextPop();

  /** Bit-blaster used to bit-blast atoms/terms. */
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

  /** Stores the current input assertions. */
  context::CDList<Node> d_assertions;

  /** Stores the SatLiteral for a given fact. */
  context::CDHashMap<Node, bitwuzla::Term> d_factLiteralCache;

  /** Reverse map of `d_factLiteralCache`. */
  context::CDHashMap<bitwuzla::Term, Node> d_literalFactCache;

  /** Option to enable/disable bit-level propagation. */
  bool d_propagate;

  /** Notifies when reset-assertion was called. */
  std::unique_ptr<NotifyResetAssertions> d_resetNotify;

  /**
   * Notifies when the SAT context is popped so we can mirror
   * the pop in bitwuzla via push()/pop().
   */
  std::unique_ptr<BitwuzlaContextNotify> d_satContextNotify;

  /** Tracks the current bitwuzla context level (number of pushes done). */
  uint32_t d_bitwuzlaLevel;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
