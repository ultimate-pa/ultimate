package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.actions;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collection;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph.GraphHandler;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.DefaultModalGraphMouse;
import edu.uci.ics.jung.visualization.control.ModalGraphMouse;

/**
 * Implements ActionListener and overrides the actionPerformed(ActionEvent)
 * method, which manages the logic for the JV context menu.
 * 
 * @see {@link ActionListener}
 * @author lena
 * 
 */
public class ContextMenuActions implements ActionListener {

	public static final String ACTION_EXPORT = "Export as SVG"; // 1
	public static final String ACTION_PICKING = "Picking";// 2
	public static final String ACTION_TRANSFORMING = "Transforming";// 3
	public static final String ACTION_KEYHELP = "Key help";// 4
	public static final String ACTION_COLLAPSE = "Collapse";// 5
	public static final String ACTION_EXTEND = "Extend";// 6

	@Override
	public void actionPerformed(ActionEvent e) {

		String actionCommmand = e.getActionCommand();

		if (actionCommmand.equals(ACTION_EXPORT)) {
			MenuActions.exportAsSVG();
		} else if (actionCommmand.equals(ACTION_PICKING)) {
			Collection<VisualizationViewer<VisualizationNode, VisualizationEdge>> openedVVs = GraphHandler
					.getInstance().getVisualizationViewers().values();
			Iterator<VisualizationViewer<VisualizationNode, VisualizationEdge>> itr = openedVVs.iterator();
			while (itr.hasNext()) {

				((DefaultModalGraphMouse<?, ?>) itr.next().getGraphMouse()).setMode(ModalGraphMouse.Mode.PICKING);
				MenuActions.setMode(ACTION_PICKING);
			}
		} else if (actionCommmand.equals(ACTION_TRANSFORMING)) {
			Collection<VisualizationViewer<VisualizationNode, VisualizationEdge>> openedVVs = GraphHandler
					.getInstance().getVisualizationViewers().values();
			Iterator<VisualizationViewer<VisualizationNode, VisualizationEdge>> itr = openedVVs.iterator();
			while (itr.hasNext()) {
				VisualizationViewer<VisualizationNode, VisualizationEdge> current = itr.next();
				DefaultModalGraphMouse<?, ?> mouse = ((DefaultModalGraphMouse<?, ?>) current.getGraphMouse());
				mouse.setMode(ModalGraphMouse.Mode.TRANSFORMING);
				MenuActions.setMode(ACTION_TRANSFORMING);
			}
		} else if (actionCommmand.equals(ACTION_KEYHELP)) {
			MenuActions.openKeyHelp();
		}

	}

}
