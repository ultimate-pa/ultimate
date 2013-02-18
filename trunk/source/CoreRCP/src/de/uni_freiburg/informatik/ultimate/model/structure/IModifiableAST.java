package de.uni_freiburg.informatik.ultimate.model.structure;

/***
 * This interface represents a modifiable variant of {@link IAST}.
 * 
 * @author dietsch
 * 
 * @param <T>
 *            is the type of the concrete model. This parameter should be used
 *            by sub-interfaces to specify a more restrictive type and thus free
 *            clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModel</tt> would declare
 *            <tt>public final class FinalModel implements IModifiableAST&lt;FinalModel&gt;</tt>
 *            .
 * @see IAST
 * @see IModifiableOutgoing
 */
public interface IModifiableAST<T extends IModifiableAST<T>> extends IAST<T>,
		IModifiableOutgoing<T> {

	/**
	 * This method changes the parent pointer of the current node. This operation
	 * may break the link between children and parent by removing or changing
	 * the parent pointer but retaining the child in the parents
	 * {@link ISimpleAST#getOutgoingNodes getOutgoingNodes()} list.
	 * 
	 * @param parent
	 *            A new parent node or null.
	 */
	void setIncomingNode(T parent);

	/**
	 * This method changes the parent pointer of the given node. This operation
	 * retains the invariants of IAST by automatically removing the current node
	 * from the {@link ISimpleAST#getOutgoingNodes list of children} of the old
	 * parent and inserting it into the list of children of the new parent. If
	 * the new parent is null, the operation will only remove the current node
	 * from the list of children of the old parent.
	 * 
	 * @param parent
	 *            A new parent or null.
	 */
	void redirectParent(T parent);
}
