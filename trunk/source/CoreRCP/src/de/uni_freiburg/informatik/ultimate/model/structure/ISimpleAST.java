package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/***
 * This interface describes a model that represents an abstract syntax tree
 * (AST). An AST is always a tree.
 * 
 * This interface only provides access to the children of the tree, for ASTs
 * with a link to the parent use the {@link IAST} interface instead.
 * 
 * This interface describes an unmodifiable AST (it provides no methods for
 * changing the tree), for a modifiable variant see {@link IModifiableSimpleAST}
 * .
 * 
 * @author dietsch
 * @param <T>
 *            is the type of the concrete model. This parameter should be used
 *            by sub-interfaces to specify a more restrictive type and thus free
 *            clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModel</tt> would declare
 *            <tt>public final class FinalModel implements ISimpleAST&lt;FinalModel&gt;</tt>
 *            .
 * @see IAST
 * @see IElement
 * @see IModifiableSimpleAST
 */
public interface ISimpleAST<T extends ISimpleAST<T>> extends IElement, IVisualizable, IWalkable {

	/***
	 * The method returns the direct successor nodes of the current AST node. If
	 * there are no successors, this method must return an empty list.
	 * 
	 * This list should be treated as not modifiable. Use it only to iterate or
	 * determine size.
	 * 
	 * @return A list containing the direct successors of the current node.
	 */
	List<T> getOutgoingNodes();
}
