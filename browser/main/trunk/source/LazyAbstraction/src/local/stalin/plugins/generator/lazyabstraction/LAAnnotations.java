/**
 * 
 */
package local.stalin.plugins.generator.lazyabstraction;

import java.util.ArrayList;

import local.stalin.model.AbstractAnnotations;

/**
 * @author alexander
 *
 */
public class LAAnnotations extends AbstractAnnotations {

	private static final long serialVersionUID = 7050640072093088882L;

	UnwindingNode m_node;
	
	/**
	 * 
	 */
	public LAAnnotations(UnwindingNode n) {
		m_node = n;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.AbstractAnnotations#getFieldNames()
	 */
	@Override
	protected String[] getFieldNames() {
		String[] s = {"is covered", "covering node", "covered nodes", "is leaf", "preorder index"}; 
		return s;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.AbstractAnnotations#getFieldValue(java.lang.String)
	 */
	@Override
	protected Object getFieldValue(String field) {
		if(field.equals("is covered"))
			return m_node.isCovered();
		else if(field.equals("covering node"))
			return m_node.get_coveringNode();
		else if(field.equals("covered nodes"))
			return m_node.get_coveredNodes();
		else if(field.equals("is leaf"))
			return m_node.isLeaf();		
		else if(field.equals("preorder index"))
			return m_node.getIndexInPreorder();
		
		return null;
	}

}
