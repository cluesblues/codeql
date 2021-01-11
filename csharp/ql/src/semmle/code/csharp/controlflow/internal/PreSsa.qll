import csharp

/**
 * Provides an SSA implementation based on "pre-basic-blocks", restricted
 * to local scope variables and fields/properties that behave like local
 * scope variables.
 */
module PreSsa {
  import pressa.SsaImplSpecific
  private import pressa.SsaImplCommon as SsaImpl

  class Definition extends SsaImpl::Definition {
    final AssignableRead getARead() { SsaImpl::ssaDefReachesRead(_, this, result, _) }

    final AssignableDefinition getDefinition() {
      exists(BasicBlock bb, int i, SourceVariable v |
        this.definesAt(v, bb, i) and
        definitionAt(result, bb, i, v)
      )
    }

    final AssignableRead getAFirstRead() {
      exists(BasicBlock bb1, int i1 |
        this.definesAt(_, bb1, i1) and
        SsaImpl::adjacentVarRead(this, bb1, i1, result)
      )
    }

    Location getLocation() {
      result = this.getDefinition().getLocation()
      or
      exists(Callable c, BasicBlock bb, SourceVariable v |
        this.definesAt(v, bb, -1) and
        implicitEntryDef(c, bb, v) and
        result = c.getLocation()
      )
    }
  }

  class PhiNode extends SsaImpl::PhiNode, Definition {
    final override Location getLocation() { result = this.getBasicBlock().getLocation() }

    final override Definition getAnInput() { result = SsaImpl::PhiNode.super.getAnInput() }
  }

  predicate adjacentReadPairSameVar(AssignableRead read1, AssignableRead read2) {
    exists(BasicBlock bb1, int i1 |
      read1 = getBasicBlockNode(bb1, i1) and
      variableRead(bb1, i1, _, _) and
      SsaImpl::adjacentVarRead(_, bb1, i1, read2)
    )
  }
}
