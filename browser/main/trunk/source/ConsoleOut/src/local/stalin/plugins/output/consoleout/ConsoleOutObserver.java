/**
 * 
 */
package local.stalin.plugins.output.consoleout;

import java.util.Map;

import org.apache.log4j.Logger;

import local.stalin.access.IManagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.access.WalkerOptions.Command;
import local.stalin.access.WalkerOptions.State;
import local.stalin.core.api.StalinServices;
import local.stalin.model.GraphType;
import local.stalin.model.IAnnotations;
import local.stalin.model.IPayload;

/**
 * This class is a AST-Visitor for creating textual representations of the tree. It creates a String.
 * 
 * @author dietsch
 * @version 0.0.1 $LastChangedDate: 2008-03-07 14:46:30 +0100 (Fr, 07 Mrz 2008) $ $LastChangedBy: dietsch $
 *          $LastChangedRevision: 497 $
 */
public class ConsoleOutObserver implements IManagedObserver {

	private static final int s_IDENT = 40;
    private static StringBuilder m_OutputBuilder;
    private static StringBuilder m_IndentBuilder;
    private static String m_Indent;
    private static String m_Output;
    private static int m_CurrentDepth;
    private boolean m_ShowAllAnnotations;
    private int m_ChildCounts[];
//	private GraphType m_GraphType;
	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

    public ConsoleOutObserver(boolean showAllAnnotationsDefault) {
        super();
        this.m_ShowAllAnnotations = showAllAnnotationsDefault;
        finish();
    }

    public void finish() {

    }

    public String getOutput() {
        if (m_Output==null) {
            if (m_OutputBuilder.toString()=="") {
            	s_Logger.error("You should run the Treewalker first.");
                return null;
            }
            m_Output = m_OutputBuilder.toString();
        }
        return m_Output;
    }

	/**
	 * @param showAllAnnotations the showAllAnnotations to set
	 */
	public void setShowAllAnnotations(boolean showAllAnnotations) {
		this.m_ShowAllAnnotations = showAllAnnotations;
	}

	protected void setInputDefinition(GraphType type){
//		m_GraphType = type;
	}
	
	//@Override
	public void init() {
        m_OutputBuilder = new StringBuilder();
        m_IndentBuilder = new StringBuilder();
        m_Output = null;
        m_Indent = "-";
        m_CurrentDepth = 0;
        m_ChildCounts = new int[10];
        m_ChildCounts[0] = 1;
	}

	//@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	//@Override
	public Command[] process(IPayload payload, State state, int childCount) {
		StringBuilder nodedescription = new StringBuilder();

		if (m_Output != null) {
			s_Logger.error("call <TextVisitor>.reset() before running again.");
			return new Command[]{Command.SKIP};
		}
		// Are we waiting for children on the next depth
		if (m_ChildCounts[m_CurrentDepth + 1] > 0) {
			// This is the awaited child.  Increase depth.			
			m_CurrentDepth++;
			m_IndentBuilder.append(m_Indent);
			if (m_CurrentDepth + 1 >= m_ChildCounts.length) {
				int[] newChildCount = new int[2*m_CurrentDepth+2];
				System.arraycopy(m_ChildCounts, 0, 
						newChildCount, 0, m_ChildCounts.length);
				m_ChildCounts = newChildCount;
			}
		} else {
			// decrease depth until we are awaiting children.
			while (m_ChildCounts[m_CurrentDepth] == 0) {
				m_CurrentDepth--;
				m_IndentBuilder
					.setLength(m_IndentBuilder.length()-m_Indent.length());
			}
		}
		m_ChildCounts[m_CurrentDepth]--;
		m_ChildCounts[m_CurrentDepth+1] = childCount;

		nodedescription.append(m_IndentBuilder).append(payload.getName());
		if (this.m_ShowAllAnnotations) {
			nodedescription.append(";");
			int j=nodedescription.toString().length();
			if(j<s_IDENT){
				j=s_IDENT-j;
			}
			else{
				j=0;
			}
			
			for (int i=j;i>0;i--){
				nodedescription.append(" ");	
			}
			
			
			if (payload.hasAnnotation()) {
				nodedescription.append(" ~~~ ");
				nodedescription.append(" Annotations: ");
				for (Map.Entry<String, IAnnotations> eOuter
						: payload.getAnnotations().entrySet()) {
					nodedescription.append(eOuter.getKey() + " -");
					for (Map.Entry<String,Object> eInner
							: eOuter.getValue().getAnnotationsAsMap().entrySet()){
						nodedescription.append(" " + eInner.getKey() + "="
								+ eInner.getValue());
					}
				}
				nodedescription.append(" ");
			}
			nodedescription.append(" ~~~ ");
			nodedescription.append(" UID: " + payload.getID() + " ");
			if (payload.hasLocation()) {
				nodedescription.append(" ~~~ ");
				nodedescription.append(" Location: ")
					.append(payload.getLocation().getFileName()).append(": ")
					.append(payload.getLocation().getStartLine()).append(" ");
			}
		}
		s_Logger.info(nodedescription.toString());
		m_OutputBuilder.append(nodedescription.toString() + ";\n");
		return new Command[]{Command.DESCEND};
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}
