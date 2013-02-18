package local.stalin.plugins.output.jungvisualization.actions;

import javax.swing.ButtonGroup;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;
import javax.swing.JRadioButtonMenuItem;

/**
 * The context menu for JV.
 * @see {@link JPopupMenu}
 * @author lena
 *
 */
public class JVContextMenu extends JPopupMenu {
	
	private static final long serialVersionUID = 1L;
	
	private ButtonGroup group = new ButtonGroup();
    private JRadioButtonMenuItem jmi_mode_p  = new JRadioButtonMenuItem("Picking");
	private JRadioButtonMenuItem jmi_mode_t  = new JRadioButtonMenuItem("Transforming");
	
	//private JMenuItem jmi_collapse = new JMenuItem("Collapse");
	//private JMenuItem jmi_extend = new JMenuItem("Extend");
	
	public JVContextMenu(){
		ContextMenuActions actions = new ContextMenuActions();
		JMenuItem jmi_export = new JMenuItem("Export as SVG");
		JMenuItem jmi_help = new JMenuItem("Key Help");
		
		if (MenuActions.getMode().equals(MenuActions.MODE_PICKING)){
			jmi_mode_p.setSelected(true);
		}
		else
		{
			jmi_mode_t.setSelected(true);
		}
		
		group.add(jmi_mode_p);
		group.add(jmi_mode_t);
		
		jmi_mode_p.addActionListener(actions);
		jmi_mode_t.addActionListener(actions);
		jmi_help.addActionListener(actions);
		jmi_export.addActionListener(actions);
		
		jmi_export.setActionCommand(ContextMenuActions.ACTION_EXPORT);
		jmi_mode_p.setActionCommand(ContextMenuActions.ACTION_PICKING);
		jmi_mode_t.setActionCommand(ContextMenuActions.ACTION_TRANSFORMING);
		jmi_help.setActionCommand(ContextMenuActions.ACTION_KEYHELP);
		
		this.add(jmi_export);
		this.addSeparator();
		this.add(jmi_mode_p);
		this.add(jmi_mode_t);
		this.addSeparator();
		this.add(jmi_help);
		//jpm.addSeparator();
		//jpm.add(jmi_collapse);
	}

}
