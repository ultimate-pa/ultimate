package de.uni_freiburg.informatik.ultimate.model.structure;

/***
 * 
 * This interface describes all tree structures, i.e. acyclic graphs that
 * consist of at most one root node with directed links to a set of subtrees.
 * 
 * Implementers must guarantee that their structure has the properties: 
 * <ul>
 * <li> Empty tree or one root node </li>
 * <li> Children are trees</li>
 * <li> No cycles </li>
 * </ul>
 * 
 * @author dietsch
 * 
 */
public interface ITree extends IWalkable {

}
