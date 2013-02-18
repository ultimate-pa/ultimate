package de.uni_freiburg.informatik.ultimate.model.structure;

/***
 * This interface represents a modifiable variant of {@link ISimpleAST}. 
 * 
 * @author dietsch
 * @param <T>
 *            is the type of the concrete model. This parameter should be used
 *            by sub-interfaces to specify a more restrictive type and thus free
 *            clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type,
 *            e.g. a (fictive) type <tt>FinalModel</tt> would declare
 *            <tt>public final class FinalModel implements IModifiableSimpleAST&lt;FinalModel&gt;</tt>
 *            .
 * @see ISimpleAST
 * @see IModifiableOutgoing
 * 
 */
public interface IModifiableSimpleAST<T extends IModifiableSimpleAST<T>>
		extends ISimpleAST<T>, IModifiableOutgoing<T> {

}
