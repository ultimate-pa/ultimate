package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces;

/**
 * A region that contains nodes that overlap the same source range, so a hierarchical insertion into the tree is not
 * possible and rewriting individual children may result in accidently overwriting non-descendant nodes. Any
 * modification except removing the whole block should usually be avoided (and maybe even that is not a good idea).
 */
public interface IPSTOverlappingRegion extends IPSTLiteralRegion {

}
