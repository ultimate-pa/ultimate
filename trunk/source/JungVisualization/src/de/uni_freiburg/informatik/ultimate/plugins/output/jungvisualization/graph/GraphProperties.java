package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph;

import java.awt.Color;
import java.awt.Font;
import java.awt.Paint;
import java.awt.Rectangle;
import java.awt.Shape;
import java.awt.font.FontRenderContext;
import java.awt.geom.Ellipse2D;
import java.awt.geom.Rectangle2D;
import java.awt.geom.RoundRectangle2D;
import java.util.ArrayList;
import java.util.LinkedHashSet;

import org.apache.commons.collections15.Transformer;
import org.apache.commons.collections15.functors.ConstantTransformer;
import org.eclipse.jface.resource.StringConverter;
import org.eclipse.swt.graphics.RGB;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences.JungPreferenceValues;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.preferences.JungPreferenceValues.EdgeLabels;
import edu.uci.ics.jung.algorithms.layout.FRLayout;
import edu.uci.ics.jung.algorithms.layout.FRLayout2;
import edu.uci.ics.jung.algorithms.layout.ISOMLayout;
import edu.uci.ics.jung.algorithms.layout.KKLayout;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.algorithms.layout.StaticLayout;
import edu.uci.ics.jung.algorithms.layout.TreeLayout;
import edu.uci.ics.jung.algorithms.shortestpath.MinimumSpanningForest2;
import edu.uci.ics.jung.graph.DelegateForest;
import edu.uci.ics.jung.graph.DelegateTree;
import edu.uci.ics.jung.graph.Forest;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.decorators.EllipseVertexShapeTransformer;
import edu.uci.ics.jung.visualization.decorators.ToStringLabeller;
import edu.uci.ics.jung.visualization.renderers.Renderer;

/**
 * Manages graph properties. Designed according to the thread-safe singleton
 * pattern.
 * 
 * @author lena
 * 
 */
public class GraphProperties {

	private static GraphProperties instance = new GraphProperties();

	private VisualizationViewer<VisualizationNode, VisualizationEdge> vv;

	public VisualizationViewer<VisualizationNode, VisualizationEdge> getVVforLayout() {
		return vv;
	}

	public static GraphProperties getInstance() {
		return instance;
	}

	/**
	 * Sets all graph properties necessary to paint the graph.
	 * 
	 * @param vv
	 *            {@link VisualizationViewer}
	 * @param graph
	 *            {@link Graph} - directed acyclic graph
	 * @param rootNode
	 *            {@link VisualizationNode}
	 * @param errorTraces
	 *            List of error traces that should be colored
	 * @param backEdges
	 *            List of IEges - backedges to be added
	 */
	@SuppressWarnings("unchecked")
	public void setGraphProperties(final VisualizationViewer<VisualizationNode, VisualizationEdge> vv,
			Graph<VisualizationNode, VisualizationEdge> graph, VisualizationNode rootNode,
			final ArrayList<LinkedHashSet<Object>> errorTraces) {
		UltimatePreferenceStore store = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		final Font font = vv.getFont();
		final FontRenderContext frc = vv.getFontMetrics(font).getFontRenderContext();
		Layout<VisualizationNode, VisualizationEdge> layout = vv.getGraphLayout();

		//set node shape and label
		if (store.getBoolean(JungPreferenceValues.LABEL_ANNOTATED_NODES)) {
			String vertexShapePreference = store.getString(JungPreferenceValues.LABEL_SHAPE_NODE);
			Transformer<VisualizationNode, Shape> vertexShapeTransformer;
			vv.getRenderContext().setVertexLabelTransformer(new ToStringLabeller<VisualizationNode>());

			if (vertexShapePreference.equalsIgnoreCase("RoundRectangle")) {
				vertexShapeTransformer = new Transformer<VisualizationNode, Shape>() {
					public Shape transform(VisualizationNode n) {
						Rectangle2D bounds = font.getStringBounds(n.toString(), frc);
						int vertexShapeLength = (int) bounds.getWidth() + 2;
						Shape vertexShape = new RoundRectangle2D.Float(-vertexShapeLength / 2, -10, vertexShapeLength,
								20, 8, 8);
						return vertexShape;
					}
				};
			} else if (vertexShapePreference.equalsIgnoreCase("Rectangle")) {
				vertexShapeTransformer = new Transformer<VisualizationNode, Shape>() {
					public Shape transform(VisualizationNode n) {
						Rectangle2D bounds = font.getStringBounds(n.toString(), frc);
						int vertexShapeLength = (int) bounds.getWidth() + 2;
						Shape vertexShape = new Rectangle(-vertexShapeLength / 2, -10, vertexShapeLength, 20);
						return vertexShape;
					}
				};
			} else {
				vertexShapeTransformer = new EllipseVertexShapeTransformer<VisualizationNode>() {
					public Shape transform(VisualizationNode n) {
						Rectangle2D bounds = font.getStringBounds(n.toString(), frc);
						int vertexShapeLength = (int) bounds.getWidth() + 2;
						Shape vertexShape = new Ellipse2D.Float(-vertexShapeLength / 2, -10, vertexShapeLength + 3, 24);
						return vertexShape;
					}

				};
			}
			vv.getRenderContext().setVertexShapeTransformer(vertexShapeTransformer);
			vv.getRenderer().getVertexLabelRenderer().setPosition(Renderer.VertexLabel.Position.CNTR);
		}
		;

		// set node coloring
		RGB rgb = StringConverter.asRGB(store.getString(JungPreferenceValues.LABEL_COLOR_NODE));
		final Color nodeFillColor = new Color(rgb.red, rgb.green, rgb.blue);

		rgb = StringConverter.asRGB(store.getString(JungPreferenceValues.LABEL_COLOR_NODE_PICKED));
		final Color nodePickedColor = new Color(rgb.red, rgb.green, rgb.blue);

		rgb = StringConverter.asRGB(store.getString(JungPreferenceValues.LABEL_COLOR_BACKGROUND));
		Color backgroundColor = new Color(rgb.red, rgb.green, rgb.blue);
		vv.setBackground(backgroundColor);

		vv.getRenderContext().setVertexFillPaintTransformer(new Transformer<VisualizationNode, Paint>() {

			@Override
			public Paint transform(VisualizationNode arg0) {
				if (vv.getPickedVertexState().isPicked(arg0)) {
					return nodeFillColor;
				} else {
					return nodePickedColor;
				}
			}
		});

		// set edge coloring
		vv.getRenderContext().setEdgeDrawPaintTransformer(new Transformer<VisualizationEdge, Paint>() {

			@Override
			public Paint transform(VisualizationEdge arg0) {
				if (vv.getPickedEdgeState().isPicked(arg0)) {
					return Color.ORANGE;
				} else if (isPartOfCex(arg0.getBacking())) {
					return Color.RED;
				} else {
					return Color.BLACK;
				}
			}

			private boolean isPartOfCex(Object backing) {
				for (LinkedHashSet<Object> trace : errorTraces) {
					if (trace.contains(backing)) {
						return true;
					}
				}
				return false;
			}
		});

		// set edge labeling
		switch (store.getEnum(JungPreferenceValues.LABEL_ANNOTATED_EDGES, EdgeLabels.class)) {
		case None:
			break;
		case Text:
			vv.getRenderContext().setEdgeLabelTransformer(new ToStringLabeller<VisualizationEdge>() {
				public String transform(VisualizationEdge edge) {
					return edge.toString();
				}
			});
			break;
		case Hashcode:
			vv.getRenderContext().setEdgeLabelTransformer(new ToStringLabeller<VisualizationEdge>() {
				public String transform(VisualizationEdge edge) {
					return Integer.toString(edge.hashCode());
				}
			});
			break;
		default:
			throw new UnsupportedOperationException("New enum value!");
		}
		vv.getRenderContext().getEdgeLabelRenderer().setRotateEdgeLabels(false);

		// set preferred Graph Layout, default Layout = KKLayout
		String prefLayout = store.getString(JungPreferenceValues.LABEL_LAYOUT);
		if (prefLayout.equalsIgnoreCase("FRLayout")) {
			layout = new FRLayout<VisualizationNode, VisualizationEdge>(graph);
		} else if (prefLayout.equalsIgnoreCase("FRLayout2")) {
			layout = new FRLayout2<VisualizationNode, VisualizationEdge>(graph);
		} else if (prefLayout.equalsIgnoreCase("ISOMLayout")) {
			layout = new ISOMLayout<VisualizationNode, VisualizationEdge>(graph);
		} else if (prefLayout.equals("KKLayout")) {
			layout = new KKLayout<VisualizationNode, VisualizationEdge>(graph);
			((KKLayout<VisualizationNode, VisualizationEdge>) layout).setMaxIterations(400);
		} else {
			@SuppressWarnings("rawtypes")
			MinimumSpanningForest2<VisualizationNode, VisualizationEdge> prim = new MinimumSpanningForest2<>(graph,
					new DelegateForest<VisualizationNode, VisualizationEdge>(),
					DelegateTree.<VisualizationNode, VisualizationEdge> getFactory(), new ConstantTransformer(1.0));

			Forest<VisualizationNode, VisualizationEdge> tree = prim.getForest();
			Layout<VisualizationNode, VisualizationEdge> layout1 = new TreeLayout<VisualizationNode, VisualizationEdge>(
					tree);
			layout = new StaticLayout<VisualizationNode, VisualizationEdge>(graph, layout1);
		}
		this.vv = vv;
		vv.setGraphLayout(layout);

	}
}
