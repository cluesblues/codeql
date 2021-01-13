/**
 * Provides a language-independant implementation of static single assignment
 * (SSA) form.
 */

private import SsaImplSpecific

cached
private module Cached {
  /**
   * Liveness analysis to restrict the size of the SSA representation.
   */
  private module Liveness {
    /**
     * A classification of variable references into reads (of a given kind) and
     * (certain or uncertain) writes.
     */
    private newtype TRefKind =
      Read(ReadKind rk) or
      Write(boolean certain) { certain = true or certain = false }

    private class RefKind extends TRefKind {
      string toString() {
        exists(ReadKind rk | this = Read(rk) and result = "read (" + rk + ")")
        or
        exists(boolean certain | this = Write(certain) and result = "write (" + certain + ")")
      }

      int getOrder() {
        this = Read(_) and
        result = 0
        or
        this = Write(_) and
        result = 1
      }
    }

    /**
     * Holds if the `i`th node of basic block `bb` is a reference to `v` of kind `k`.
     */
    private predicate ref(BasicBlock bb, int i, SourceVariable v, RefKind k) {
      exists(ReadKind rk | variableRead(bb, i, v, rk) | k = Read(rk))
      or
      exists(boolean certain | variableWrite(bb, i, v, certain) | k = Write(certain))
    }

    private newtype OrderedRefIndex =
      MkOrderedRefIndex(int i, int tag) {
        exists(RefKind rk | ref(_, i, _, rk) | tag = rk.getOrder())
      }

    private OrderedRefIndex refOrd(BasicBlock bb, int i, SourceVariable v, RefKind k, int ord) {
      ref(bb, i, v, k) and
      result = MkOrderedRefIndex(i, ord) and
      ord = k.getOrder()
    }

    /**
     * Gets the (1-based) rank of the reference to `v` at the `i`th node of
     * basic block `bb`, which has the given reference kind `k`.
     *
     * Reads are considered before writes when they happen at the same index.
     */
    private int refRank(BasicBlock bb, int i, SourceVariable v, RefKind k) {
      refOrd(bb, i, v, k, _) =
        rank[result](int j, int ord, OrderedRefIndex res |
          res = refOrd(bb, j, v, _, ord)
        |
          res order by j, ord
        )
    }

    private int maxRefRank(BasicBlock bb, SourceVariable v) {
      result = refRank(bb, _, v, _) and
      not result + 1 = refRank(bb, _, v, _)
    }

    /**
     * Gets the (1-based) rank of the first reference to `v` inside basic block `bb`
     * that is either a read or a certain write.
     */
    private int firstReadOrCertainWrite(BasicBlock bb, SourceVariable v) {
      result =
        min(int r, RefKind k |
          r = refRank(bb, _, v, k) and
          k != Write(false)
        |
          r
        )
    }

    /**
     * Holds if source variable `v` is live at the beginning of basic block `bb`.
     * The read that witnesses the liveness of `v` is of kind `rk`.
     */
    predicate liveAtEntry(BasicBlock bb, SourceVariable v, ReadKind rk) {
      // The first read or certain write to `v` inside `bb` is a read
      refRank(bb, _, v, Read(rk)) = firstReadOrCertainWrite(bb, v)
      or
      // There is no certain write to `v` inside `bb`, but `v` is live at entry
      // to a successor basic block of `bb`
      not exists(firstReadOrCertainWrite(bb, v)) and
      liveAtExit(bb, v, rk)
    }

    /**
     * Holds if source variable `v` is live at the end of basic block `bb`.
     * The read that witnesses the liveness of `v` is of kind `rk`.
     */
    predicate liveAtExit(BasicBlock bb, SourceVariable v, ReadKind rk) {
      liveAtEntry(bb.getASuccessor(), v, rk)
    }

    /**
     * Holds if variable `v` is live in basic block `bb` at index `i`.
     * The rank of `i` is `rnk` as defined by `refRank()`.
     */
    private predicate liveAtRank(BasicBlock bb, int i, SourceVariable v, int rnk, ReadKind rk) {
      exists(RefKind kind | rnk = refRank(bb, i, v, kind) |
        rnk = maxRefRank(bb, v) and
        liveAtExit(bb, v, rk)
        or
        ref(bb, i, v, kind) and
        kind = Read(rk)
        or
        exists(RefKind nextKind |
          liveAtRank(bb, _, v, rnk + 1, rk) and
          rnk + 1 = refRank(bb, _, v, nextKind) and
          nextKind != Write(true)
        )
      )
    }

    /**
     * Holds if variable `v` is live after the (certain or uncertain) write at
     * index `i` inside basic block `bb`. The read that witnesses the liveness of
     * `v` is of kind `rk`.
     */
    predicate liveAfterWrite(BasicBlock bb, int i, SourceVariable v, ReadKind rk) {
      exists(int rnk | rnk = refRank(bb, i, v, Write(_)) | liveAtRank(bb, i, v, rnk, rk))
    }
  }

  private import Liveness

  pragma[noinline]
  private predicate phiNodeMaybeLive(BasicBlock bb, SourceVariable v) {
    exists(Definition def, BasicBlock bb1 | def.definesAt(v, bb1, _) | bb1.inDominanceFrontier(bb))
  }

  cached
  newtype TDefinition =
    TWriteDef(SourceVariable v, BasicBlock bb, int i) {
      variableWrite(bb, i, v, _) and
      liveAfterWrite(bb, i, v, _)
    } or
    TPhiNode(SourceVariable v, BasicBlock bb) {
      phiNodeMaybeLive(bb, v) and
      liveAtEntry(bb, v, _)
    }

  private module SsaDefReaches {
    /**
     * A classification of SSA variable references into reads definitions.
     */
    newtype TSsaRefKind =
      SsaRead() or
      SsaDef()

    class SsaRefKind extends TSsaRefKind {
      string toString() {
        this = SsaRead() and
        result = "SsaRead"
        or
        this = SsaDef() and
        result = "SsaDef"
      }

      int getOrder() {
        this = SsaRead() and
        result = 0
        or
        this = SsaDef() and
        result = 1
      }
    }

    /**
     * Holds if the `i`th node of basic block `bb` is a reference to `v`,
     * either a read (when `k` is `Read()`) or an SSA definition (when `k`
     * is `SsaDef()`).
     */
    predicate ssaRef(BasicBlock bb, int i, SourceVariable v, SsaRefKind k) {
      variableRead(bb, i, v, _) and
      k = SsaRead()
      or
      exists(Definition def | def.definesAt(v, bb, i)) and
      k = SsaDef()
    }

    private newtype OrderedSsaRefIndex =
      MkOrderedSsaRefIndex(int i, SsaRefKind k) { ssaRef(_, i, _, k) }

    private OrderedSsaRefIndex ssaRefOrd(
      BasicBlock bb, int i, SourceVariable v, SsaRefKind k, int ord
    ) {
      ssaRef(bb, i, v, k) and
      result = MkOrderedSsaRefIndex(i, k) and
      ord = k.getOrder()
    }

    /**
     * Gets the (1-based) rank of the reference to `v` at the `i`th node of basic
     * block `bb`, which has the given reference kind `k`.
     *
     * For example, if `bb` is a basic block with a phi node for `v` (considered
     * to be at index -1), reads `v` at node 2, and defines it at node 5, we have:
     *
     * ```ql
     * ssaRefRank(bb, -1, v, SsaDef()) = 1    // phi node
     * ssaRefRank(bb,  2, v, Read())   = 2    // read at node 2
     * ssaRefRank(bb,  5, v, SsaDef()) = 3    // definition at node 5
     * ```
     *
     * Reads are considered before writes when they happen at the same index.
     */
    int ssaRefRank(BasicBlock bb, int i, SourceVariable v, SsaRefKind k) {
      ssaRefOrd(bb, i, v, k, _) =
        rank[result](int j, int ord, OrderedSsaRefIndex res |
          res = ssaRefOrd(bb, j, v, _, ord)
        |
          res order by j, ord
        )
    }

    int maxSsaRefRank(BasicBlock bb, SourceVariable v) {
      result = ssaRefRank(bb, _, v, _) and
      not result + 1 = ssaRefRank(bb, _, v, _)
    }

    /**
     * Holds if the SSA definition `def` reaches rank index `rnk` in its own
     * basic block `bb`.
     */
    predicate ssaDefReachesRank(BasicBlock bb, Definition def, int rnk, SourceVariable v) {
      exists(int i |
        rnk = ssaRefRank(bb, i, v, SsaDef()) and
        def.definesAt(v, bb, i)
      )
      or
      ssaDefReachesRank(bb, def, rnk - 1, v) and
      rnk = ssaRefRank(bb, _, v, SsaRead())
    }

    /**
     * Holds if the SSA definition of `v` at `def` reaches `read` in the
     * same basic block without crossing another SSA definition of `v`.
     *
     * The read at `node` is of kind `rk`.
     */
    predicate ssaDefReachesReadWithinBlock(
      SourceVariable v, Definition def, ControlFlowNode read, ReadKind rk
    ) {
      exists(BasicBlock bb, int rnk, int i |
        ssaDefReachesRank(bb, def, rnk, v) and
        rnk = ssaRefRank(bb, i, v, SsaRead()) and
        variableRead(bb, i, v, rk) and
        read = getBasicBlockNode(bb, i)
      )
    }

    /**
     * Holds if the SSA definition of `v` at `def` reaches uncertain SSA definition
     * `redef` in the same basic block, without crossing another SSA definition of `v`.
     */
    predicate ssaDefReachesUncertainDefWithinBlock(
      SourceVariable v, Definition def, UncertainWriteDefinition redef
    ) {
      exists(BasicBlock bb, int rnk, int i |
        ssaDefReachesRank(bb, def, rnk, v) and
        rnk = ssaRefRank(bb, i, v, SsaDef()) - 1 and
        redef.definesAt(v, bb, i)
      )
    }

    /**
     * Same as `ssaRefRank()`, but restricted to a particular SSA definition `def`.
     */
    int ssaDefRank(Definition def, SourceVariable v, BasicBlock bb, int i, SsaRefKind k) {
      v = def.getSourceVariable() and
      result = ssaRefRank(bb, i, v, k) and
      (
        ssaDefReachesRead(_, def, getBasicBlockNode(bb, i), _)
        or
        def.definesAt(_, bb, i)
      )
    }

    predicate varOccursInBlock(Definition def, BasicBlock bb, SourceVariable v) {
      exists(ssaDefRank(def, v, bb, _, _))
    }

    pragma[noinline]
    private BasicBlock getASuccessorDefMaybeLive(Definition def, BasicBlock bb) {
      result = bb.getASuccessor() and
      not varOccursInBlock(_, bb, def.getSourceVariable()) and
      ssaDefReachesEndOfBlock(bb, def, _)
    }

    pragma[noinline]
    private predicate varOccursOrIsDeadInBlock(Definition def, BasicBlock bb) {
      varOccursInBlock(def, bb, _)
      or
      (
        varOccursInBlock(def, bb.getAPredecessor(), _)
        or
        bb = getASuccessorDefMaybeLive(def, _)
      ) and
      not varOccursInBlock(def, bb, _) and
      not ssaDefReachesEndOfBlock(bb, def, _)
    }

    private newtype DefBB =
      MkDefBB(Definition def, BasicBlock bb) {
        varOccursInBlock(def, bb.getAPredecessor(), _)
        or
        bb = getASuccessorDefMaybeLive(def, _)
      }

    pragma[noinline]
    private predicate source(Definition def, DefBB source) {
      exists(BasicBlock bb |
        varOccursInBlock(def, bb.getAPredecessor(), _) and
        source = MkDefBB(def, bb)
      )
    }

    pragma[noinline]
    private predicate sink(Definition def, DefBB sink) {
      exists(BasicBlock bb |
        varOccursOrIsDeadInBlock(def, bb) and
        sink = MkDefBB(def, bb)
      )
    }

    private predicate succ(DefBB pred, DefBB succ) {
      exists(Definition def, BasicBlock bbPred |
        pred = MkDefBB(def, bbPred) and
        succ = MkDefBB(def, getASuccessorDefMaybeLive(def, bbPred))
      )
    }

    private predicate succPlus(DefBB pred, DefBB succ) = fastTC(succ/2)(pred, succ)

    pragma[noinline]
    private predicate varBlockReachesPlus(Definition def, DefBB bb1, DefBB bb2) {
      source(def, bb1) and
      sink(def, bb2) and
      succPlus(bb1, bb2)
    }

    /**
     * Holds if `def` is accessed in basic block `bb1` (either a read or a write),
     * `bb2` is a transitive successor of `bb1`, `def` is live at the end of `bb1`,
     * and the underlying variable for `def` is neither read nor written in any block
     * on a path between `bb1` and `bb2`.
     *
     * Moreover, either `def` is accessed in `bb2`, or `def` is no longer live in
     * `bb2`.
     */
    private predicate varBlockReaches(Definition def, BasicBlock bb1, BasicBlock bb2) {
      varOccursInBlock(def, bb1, _) and
      exists(BasicBlock succ | succ = bb1.getASuccessor() |
        varOccursOrIsDeadInBlock(def, succ) and
        bb2 = succ
        or
        varBlockReachesPlus(def, MkDefBB(def, succ), MkDefBB(def, bb2))
      )
    }

    /**
     * Holds if `def` is accessed in basic block `bb` (either a read or a write),
     * `def` is read at `read`, `read` is in a transitive successor block of `bb`,
     * and `def` is neither read nor written in any block on a path between `bb`
     * and `read`.
     */
    predicate defAdjacentRead(Definition def, BasicBlock bb, ControlFlowNode read) {
      exists(BasicBlock bb2, int i2 |
        varBlockReaches(def, bb, bb2) and
        ssaRefRank(bb2, i2, def.getSourceVariable(), SsaRead()) = 1 and
        variableRead(bb2, i2, _, _) and
        read = getBasicBlockNode(bb2, i2)
      )
    }

    /**
     * Holds if `def` is accessed in basic block `bb` (either a read or a write),
     * the underlying variable is redefined at `redef`, `redef` is in a transitive
     * successor block of `bb`, and `def` is neither read nor written in any block
     * on a path between `bb` and `redef`.
     */
    predicate defAdjacentRedef(Definition def, BasicBlock bb, Definition redef) {
      exists(BasicBlock bb2, int j, SourceVariable v |
        v = def.getSourceVariable() and
        varBlockReaches(def, bb, bb2) and
        redef.definesAt(v, bb2, j) and
        1 = ssaRefRank(bb2, j, v, SsaDef())
      )
    }

    pragma[noinline]
    private predicate isDeadAt(Definition def, BasicBlock bb) {
      varBlockReaches(def, _, bb) and
      not varOccursInBlock(def, bb, _)
    }

    /**
     * Holds if `def` is accessed in basic block `bb` (either a read or a write) and
     * `bb` can reach the end of the enclosing callable, without passing through another
     * read or write.
     */
    predicate defDead(Definition def, BasicBlock bb) {
      exists(BasicBlock bb2 | varBlockReaches(def, bb, bb2) and isDeadAt(def, bb2))
    }
  }

  /**
   * Holds if `def` is accessed at index `i1` in basic block `bb1` (either a read
   * or a write), `def` is read at `read`, and there is a path between them without
   * any read of `def`.
   */
  cached
  predicate adjacentVarRead(Definition def, BasicBlock bb1, int i1, ControlFlowNode read) {
    exists(int rnk, int i2 |
      rnk = ssaDefRank(def, _, bb1, i1, _) and
      rnk + 1 = ssaDefRank(def, _, bb1, i2, SsaRead()) and
      variableRead(bb1, i2, _, _) and
      read = getBasicBlockNode(bb1, i2)
    )
    or
    exists(SourceVariable v | ssaDefRank(def, v, bb1, i1, _) = maxSsaRefRank(bb1, v)) and
    defAdjacentRead(def, bb1, read)
  }

  private import SsaDefReaches

  pragma[noinline]
  private predicate ssaDefReachesEndOfBlockRec(BasicBlock bb, Definition def, SourceVariable v) {
    exists(BasicBlock idom | ssaDefReachesEndOfBlock(idom, def, v) |
      // The construction of SSA form ensures that each read of a variable is
      // dominated by its definition. An SSA definition therefore reaches a
      // control flow node if it is the _closest_ SSA definition that dominates
      // the node. If two definitions dominate a node then one must dominate the
      // other, so therefore the definition of _closest_ is given by the dominator
      // tree. Thus, reaching definitions can be calculated in terms of dominance.
      idom = getImmediateDominator(bb)
    )
  }

  /**
   * Holds if the SSA definition of `v` at `def` reaches the end of basic
   * block `bb`, at which point it is still live, without crossing another
   * SSA definition of `v`.
   */
  cached
  predicate ssaDefReachesEndOfBlock(BasicBlock bb, Definition def, SourceVariable v) {
    exists(int last | last = maxSsaRefRank(bb, v) |
      ssaDefReachesRank(bb, def, last, v) and
      liveAtExit(bb, v, _)
    )
    or
    ssaDefReachesEndOfBlockRec(bb, def, v) and
    liveAtExit(bb, v, _) and
    not ssaRef(bb, _, v, SsaDef())
  }

  /**
   * Holds if the SSA definition of `v` at `def` reaches `read` without crossing
   * another SSA definition of `v`. The read at `read` is of kind `rk`.
   */
  cached
  predicate ssaDefReachesRead(SourceVariable v, Definition def, ControlFlowNode read, ReadKind rk) {
    ssaDefReachesReadWithinBlock(v, def, read, rk)
    or
    exists(BasicBlock bb, int i |
      variableRead(bb, i, v, rk) and
      read = getBasicBlockNode(bb, i) and
      ssaDefReachesEndOfBlock(bb.getAPredecessor(), def, v) and
      not ssaDefReachesReadWithinBlock(v, _, read, _)
    )
  }

  /**
   * Holds if the SSA definition of `v` at `def` reaches uncertain SSA definition
   * `redef` without crossing another SSA definition of `v`.
   */
  cached
  predicate ssaDefReachesUncertainDef(
    SourceVariable v, Definition def, UncertainWriteDefinition redef
  ) {
    ssaDefReachesUncertainDefWithinBlock(v, def, redef)
    or
    exists(BasicBlock bb |
      redef.definesAt(v, bb, _) and
      ssaDefReachesEndOfBlock(bb.getAPredecessor(), def, v) and
      not ssaDefReachesUncertainDefWithinBlock(v, _, redef)
    )
  }

  /**
   * Holds if the node at index `i` in `bb` is a last reference to SSA definition
   * `def`. The reference is last because it can reach the end of the enclosing
   * callable, without passing through another read or write.
   */
  cached
  predicate lastRefExit(Definition def, BasicBlock bb, int i) {
    exists(SourceVariable v | ssaDefRank(def, v, bb, i, _) = maxSsaRefRank(bb, v) |
      // Can reach exit directly
      bb instanceof ExitBasicBlock
      or
      // Can reach a block using one or more steps, where `def` is no longer live
      defDead(def, bb)
    )
  }

  /**
   * Holds if the node at index `i` in `bb` is a last reference to SSA definition
   * `def`. The reference is last because it can reach another write `next`,
   * without passing through another read or write.
   */
  cached
  predicate lastRefRedef(Definition def, BasicBlock bb, int i, Definition next) {
    exists(int rnk, SourceVariable v | rnk = ssaDefRank(def, v, bb, i, _) |
      // Next reference to `v` inside `bb` is a write
      exists(int j |
        next.definesAt(v, bb, j) and
        rnk + 1 = ssaRefRank(bb, j, v, SsaDef())
      )
      or
      // Can reach a write using one or more steps
      rnk = maxSsaRefRank(bb, v) and
      defAdjacentRedef(def, bb, next)
    )
  }
}

import Cached

/** A static single assignment (SSA) definition. */
class Definition extends TDefinition {
  /** Gets the source variable underlying this SSA definition. */
  SourceVariable getSourceVariable() { this.definesAt(result, _, _) }

  /**
   * Holds is this SSA definition is live at the end of basic block `bb`.
   * That is, this definition reaches the end of basic block `bb`, at which
   * point it is still live, without crossing another SSA definition of the
   * same source variable.
   */
  final predicate isLiveAtEndOfBlock(BasicBlock bb) { ssaDefReachesEndOfBlock(bb, this, _) }

  /**
   * Holds if this SSA definition defines `v` at index `i` in basic block `bb`.
   * Phi nodes are considered to be at index `-1`, while normal variable writes
   * are at the index of the control flow node they wrap.
   */
  final predicate definesAt(SourceVariable v, BasicBlock bb, int i) {
    this = TWriteDef(v, bb, i)
    or
    this = TPhiNode(v, bb) and i = -1
  }

  /** Gets the basic block to which this SSA definition belongs. */
  final BasicBlock getBasicBlock() { this.definesAt(_, result, _) }

  /**
   * Gets the control flow node of this SSA definition, if any. Phi nodes are
   * examples of SSA definitions without a control flow node, as they are
   * modelled at index `-1` in the relevant basic block.
   */
  final ControlFlowNode getControlFlowNode() {
    exists(BasicBlock bb, int i | this.definesAt(_, bb, i) | result = getBasicBlockNode(bb, i))
  }

  /**
   * Gets an SSA definition whose value can flow to this one in one step. This
   * includes inputs to phi nodes and the prior definitions of uncertain writes.
   */
  private Definition getAPseudoInputOrPriorDefinition() {
    result = this.(PhiNode).getAnInput() or
    result = this.(UncertainWriteDefinition).getPriorDefinition()
  }

  /**
   * Gets a definition that ultimately defines this SSA definition and is
   * not itself a phi node.
   */
  Definition getAnUltimateDefinition() {
    result = this.getAPseudoInputOrPriorDefinition*() and
    not result instanceof PhiNode
  }

  /** Gets a textual representation of this SSA definition. */
  string toString() { none() }
}

/** An SSA definition that corresponds to a write. */
class WriteDefinition extends Definition, TWriteDef {
  private SourceVariable v;
  private BasicBlock bb;
  private int i;

  WriteDefinition() { this = TWriteDef(v, bb, i) }

  override string toString() { result = "WriteDef" }
}

/** A phi node. */
class PhiNode extends Definition, TPhiNode {
  /** Gets an input of this phi node. */
  Definition getAnInput() {
    exists(BasicBlock bb, BasicBlock phiPred, SourceVariable v |
      this.definesAt(v, bb, _) and
      bb.getAPredecessor() = phiPred and
      ssaDefReachesEndOfBlock(phiPred, result, v)
    )
  }

  /** Holds if `inp` is an input to the phi node along the edge originating in `bb`. */
  predicate hasInputFromBlock(Definition inp, BasicBlock bb) {
    this.getAnInput() = inp and
    this.getBasicBlock().getAPredecessor() = bb and
    inp.isLiveAtEndOfBlock(bb)
  }

  override string toString() { result = "Phi" }
}

/**
 * An SSA definition that represents an uncertain update of the underlying
 * source variable.
 */
class UncertainWriteDefinition extends WriteDefinition {
  UncertainWriteDefinition() {
    exists(SourceVariable v, BasicBlock bb, int i |
      this.definesAt(v, bb, i) and
      variableWrite(bb, i, v, false)
    )
  }

  /**
   * Gets the immediately preceding definition. Since this update is uncertain,
   * the value from the preceding definition might still be valid.
   */
  Definition getPriorDefinition() { ssaDefReachesUncertainDef(_, result, this) }
}
