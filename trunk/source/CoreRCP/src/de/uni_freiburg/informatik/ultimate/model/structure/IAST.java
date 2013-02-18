package de.uni_freiburg.informatik.ultimate.model.structure;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/***
 * This interface describes a model of an abstract syntax tree (AST) according
 * to {@link ISimpleAST} and extends it with an explicit pointer from each node
 * to its parent node.
 * 
 * For ASTs without a link to the parent use the {@link ISimpleAST} interface
 * instead.
 * 
 * This interface describes an unmodifiable AST (it provides no methods for
 * changing the tree), for a modifiable variant see
 * {@link IModifiableAST}.
 * 
 * @author dietsch
 * @param <T>
 *            is the type of the concrete model. This parameter should be used
 *            by sub-interfaces to specify a more restrictive type and thus free
 *            clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModel</tt> would declare
 *            <tt>public final class FinalModel implements IAST&lt;FinalModel&gt;</tt>.
 * @see ISimpleAST
 * @see IElement
 */

public interface IAST<T extends IAST<T>> extends ISimpleAST<T> {
	/**
	 * This method returns the direct predecessor of this node (the parent). If
	 * this node is the root node of the tree, this method must return null.
	 * 
	 * @return The parent node of this node or null, if this node is the root
	 *         node.
	 */
	T getIncomingNode();
}