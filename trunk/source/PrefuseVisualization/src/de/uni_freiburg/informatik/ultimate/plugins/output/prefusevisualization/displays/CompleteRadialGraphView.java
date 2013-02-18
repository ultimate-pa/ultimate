package de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.displays;

import java.awt.geom.Point2D;

import prefuse.Constants;
import prefuse.Display;
import prefuse.Visualization;
import prefuse.action.ActionList;
import prefuse.action.ItemAction;
import prefuse.action.RepaintAction;
import prefuse.action.animate.ColorAnimator;
import prefuse.action.animate.LocationAnimator;
import prefuse.action.animate.PolarLocationAnimator;
import prefuse.action.animate.QualityControlAnimator;
import prefuse.action.animate.VisibilityAnimator;
import prefuse.action.assignment.ColorAction;
import prefuse.action.assignment.FontAction;
import prefuse.action.layout.CollapsedSubtreeLayout;
import prefuse.action.layout.graph.RadialTreeLayout;
import prefuse.activity.Activity;
import prefuse.activity.SlowInSlowOutPacer;
import prefuse.controls.DragControl;
import prefuse.controls.FocusControl;
import prefuse.controls.HoverActionControl;
import prefuse.controls.PanControl;
import prefuse.controls.ZoomControl;
import prefuse.controls.ZoomToFitControl;
import prefuse.data.Graph;
import prefuse.render.AbstractShapeRenderer;
import prefuse.render.DefaultRendererFactory;
import prefuse.render.EdgeRenderer;
import prefuse.render.LabelRenderer;
import prefuse.visual.VisualItem;
import prefuse.visual.expression.InGroupPredicate;
import prefuse.visual.sort.TreeDepthItemSorter;

import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.actions.AutoPanAction;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.actions.EdgeLabel;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.actions.NodeMarkAction;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.actions.TextMarkAction;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui.PrefuseColorSelection;
import de.uni_freiburg.informatik.ultimate.plugins.output.prefusevisualization.gui.PrefuseFontSelection;

/**
 * prefuse radial display with rotate action
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-07 13:50:06 +0100 (Fr, 07 Mrz 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 495 $
 */
public class CompleteRadialGraphView extends Display {

	private static final long serialVersionUID = 1L;
	private static final String tree = "tree";
	private static final String treeNodes = "tree.nodes";
	private static final String treeEdges = "tree.edges";
	private static final String linear = "linear";

	private LabelRenderer m_nodeRenderer;
	private EdgeRenderer m_edgeRenderer;

	private PrefuseFontSelection prefuseFontSelection = new PrefuseFontSelection();
	private PrefuseColorSelection prefuseColorSelection = new PrefuseColorSelection();

	private String m_label = "label";

	/**
	 * @param g
	 *            Graph object to display
	 * @param label
	 *            label
	 */
	public CompleteRadialGraphView(Graph g, String label) {
		super(new Visualization());
		m_label = label;

		// -- set up visualization --
		m_vis.add(tree, g);
		m_vis.setInteractive(treeEdges, null, false);

		// -- set up renderers --
		m_nodeRenderer = new LabelRenderer(m_label);
		m_nodeRenderer.setRenderType(AbstractShapeRenderer.RENDER_TYPE_FILL);
		m_nodeRenderer.setHorizontalAlignment(Constants.CENTER);
		m_nodeRenderer.setRoundedCorner(8, 8);
		m_edgeRenderer = new EdgeRenderer();

		DefaultRendererFactory rf = new DefaultRendererFactory(m_nodeRenderer);
		rf.add(new InGroupPredicate(treeEdges), m_edgeRenderer);
		m_vis.setRendererFactory(rf);

		m_vis.addDecorators("name", treeEdges, EdgeLabel.getDecorator());

		// -- set up processing actions --

		// colors
		ItemAction nodeColor = new NodeMarkAction(treeNodes);
		ItemAction textColor = new TextMarkAction(treeNodes);
		m_vis.putAction("textColor", textColor);

		ItemAction edgeColor = new ColorAction(treeEdges,
				VisualItem.STROKECOLOR, prefuseColorSelection
						.getEdgeStyleColor());

		FontAction fonts = new FontAction(treeNodes, prefuseFontSelection
				.getNodeFont());

		// recolor
		ActionList recolor = new ActionList();
		recolor.add(nodeColor);
		recolor.add(textColor);
		m_vis.putAction("recolor", recolor);

		// repaint
		ActionList repaint = new ActionList();
		repaint.add(recolor);
		repaint.add(new RepaintAction());
		m_vis.putAction("repaint", repaint);

		// animate paint change
		ActionList animatePaint = new ActionList(400);
		animatePaint.add(new ColorAnimator(treeNodes));
		animatePaint.add(new RepaintAction());
		m_vis.putAction("animatePaint", animatePaint);

		// create the tree layout action
		RadialTreeLayout treeLayout = new RadialTreeLayout(tree);
		treeLayout.setLayoutAnchor(new Point2D.Double(400, 400));
		treeLayout.setAutoScale(false);
		treeLayout.setRadiusIncrement(10 * prefuseFontSelection
				.getDistanceFaktor());

		m_vis.putAction("treeLayout", treeLayout);

		CollapsedSubtreeLayout subLayout = new CollapsedSubtreeLayout(tree);
		m_vis.putAction("subLayout", subLayout);

		AutoPanAction autoPan = new AutoPanAction(this, Constants.ORIENT_CENTER);

		// render edge labels
		ActionList layout = new ActionList(Activity.INFINITY);
		layout.add(new EdgeLabel("name"));
		layout.add(autoPan);
		m_vis.putAction("layout", layout);
		m_vis.run("layout");

		// create orientation
		ActionList orient = new ActionList(2000);
		orient.setPacingFunction(new SlowInSlowOutPacer());
		orient.add(autoPan);
		orient.add(new QualityControlAnimator());
		orient.add(new LocationAnimator(treeNodes));
		orient.add(new RepaintAction());
		m_vis.putAction("orient", orient);

		// create the filtering and layout
		ActionList filter = new ActionList();
		filter.add(fonts);
		filter.add(treeLayout);
		filter.add(subLayout);
		filter.add(textColor);
		filter.add(nodeColor);
		filter.add(edgeColor);
		m_vis.putAction("filter", filter);

		// animated transition
		ActionList animate = new ActionList(1000);
		animate.setPacingFunction(new SlowInSlowOutPacer());
		animate.add(autoPan);
		animate.add(new QualityControlAnimator());
		animate.add(new VisibilityAnimator(tree));
		animate.add(new PolarLocationAnimator(treeNodes, linear));
		animate.add(new LocationAnimator(treeNodes));
		animate.add(new ColorAnimator(treeNodes));
		animate.add(new RepaintAction());
		m_vis.putAction("animate", animate);
		m_vis.alwaysRunAfter("filter", "animate");

		// initialize the display
		setItemSorter(new TreeDepthItemSorter());
		addControlListener(new DragControl());
		addControlListener(new ZoomToFitControl());
		addControlListener(new ZoomControl());
		addControlListener(new PanControl());
		addControlListener(new FocusControl(1, "filter"));
		addControlListener(new HoverActionControl("repaint"));

		// filter graph and perform layout
		m_vis.run("filter");
	}
}