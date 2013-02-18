package local.stalin.plugins.output.jungvisualization.graph;

import java.awt.Color;
import java.awt.Font;
import java.awt.Rectangle;
import java.awt.Shape;
import java.awt.font.FontRenderContext;
import java.awt.geom.Ellipse2D;
import java.awt.geom.Rectangle2D;
import java.awt.geom.RoundRectangle2D;
import java.util.List;

import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.plugins.output.jungvisualization.Activator;
import local.stalin.plugins.output.jungvisualization.layout.TestLayout;
import local.stalin.plugins.output.jungvisualization.layout.TestLayout2;
import local.stalin.plugins.output.jungvisualization.preferences.PreferenceValues;

import org.apache.commons.collections15.Transformer;
import org.apache.commons.collections15.functors.ConstantTransformer;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

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
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.decorators.EdgeShape;
import edu.uci.ics.jung.visualization.decorators.EllipseVertexShapeTransformer;
import edu.uci.ics.jung.visualization.decorators.PickableVertexPaintTransformer;
import edu.uci.ics.jung.visualization.decorators.ToStringLabeller;
import edu.uci.ics.jung.visualization.picking.ClosestShapePickSupport;
import edu.uci.ics.jung.visualization.renderers.Renderer;
import edu.uci.ics.jung.visualization.transform.shape.GraphicsDecorator;

/**
 * Manages graph properties.
 * Designed according to the thread-safe singleton pattern.
 * @author lena
 *
 */
public class GraphProperties {
	
	private static GraphProperties instance = new GraphProperties();
	
	private VisualizationViewer<INode, IEdge> vv;
	public VisualizationViewer<INode, IEdge> getVVforLayout()
	{
		return vv;
	}
	public static GraphProperties getInstance(){
		return instance;
	}
	
	/**
	 * Sets all graph properties necessary to paint the graph.
	 * @param vv {@link VisualizationViewer}
	 * @param graph {@link Graph} - directed acyclic graph
	 * @param rootNode {@link INode}
	 * @param backEdges List of IEges - backedges to be added
	 */
	@SuppressWarnings("unchecked")
	public void setGraphProperties(VisualizationViewer<INode, IEdge> vv, Graph<INode,IEdge> graph, INode rootNode){
		ConfigurationScope scope = new ConfigurationScope();
		IEclipsePreferences prefs = scope.getNode(Activator.PLUGIN_ID);
		ScopedPreferenceStore store = PreferenceValues.Preference;
		final Font font = vv.getFont();
		final FontRenderContext frc = vv.getFontMetrics(font).getFontRenderContext();
		Layout<INode, IEdge> layout = vv.getGraphLayout();
		

		Transformer<INode,Shape> vertexShapeTransformer;
		String vertexShapePreference = prefs.get(PreferenceValues.NAME_SHAPE_NODE, PreferenceValues.VALUE_SHAPE_NODE_DEFAULT);
		
		//TODO:testing
//		 MinimumSpanningForest2<INode,IEdge> prim = 
//	        	new MinimumSpanningForest2<INode,IEdge>(graph,
//	        		new DelegateForest<INode,IEdge>(), DelegateTree.<INode,IEdge>getFactory(),
//	        		new ConstantTransformer(1.0));
//	        
//	        Forest<INode,IEdge> tree = prim.getForest();
	        //Layout<INode,IEdge> layout1 = new TestLayout(tree,backEdges,rootNode);
		//end testing

		if (prefs.getBoolean(PreferenceValues.NAME_ANNOTATED_NODES, PreferenceValues.VALUE_ANNOTATED_NODES_DEFAULT)){
			vv.getRenderContext().setVertexLabelTransformer(new ToStringLabeller<INode>());

			if (vertexShapePreference.equalsIgnoreCase("RoundRectangle")){
				vertexShapeTransformer = new Transformer<INode,Shape>() {
					public Shape transform(INode n) {
						Rectangle2D bounds = font.getStringBounds(n.toString(), frc);
						int vertexShapeLength = (int) bounds.getWidth()+2;
						Shape vertexShape = new RoundRectangle2D.Float(-vertexShapeLength/2, -10, vertexShapeLength, 20, 8, 8);
						return vertexShape;
					}
				};	
			}
			else if (vertexShapePreference.equalsIgnoreCase("Rectangle")){
				vertexShapeTransformer = new Transformer<INode,Shape>() {
					public Shape transform(INode n) {
						Rectangle2D bounds = font.getStringBounds(n.toString(), frc);
						int vertexShapeLength = (int) bounds.getWidth()+2;
						Shape vertexShape =  new Rectangle(-vertexShapeLength/2, -10, vertexShapeLength, 20);
						return vertexShape;
					}
				};	
			}
			else{
				vertexShapeTransformer = new EllipseVertexShapeTransformer<INode>(){
					public Shape transform(INode n) {
						Rectangle2D bounds = font.getStringBounds(n.toString(), frc);
						int vertexShapeLength = (int) bounds.getWidth()+2;
						Shape vertexShape =  new Ellipse2D.Float(-vertexShapeLength/2, -10, vertexShapeLength+3, 24);
						return vertexShape;
					}

				};
			}
			vv.getRenderContext().setVertexShapeTransformer(vertexShapeTransformer);
			vv.getRenderer().getVertexLabelRenderer().setPosition(Renderer.VertexLabel.Position.CNTR);
		}
		
		RGB rgb = PreferenceConverter.getColor(store, PreferenceValues.NAME_COLOR_NODE);
		Color nodeFillColor = new Color(rgb.red,rgb.green,rgb.blue);
		rgb = PreferenceConverter.getColor(store, PreferenceValues.NAME_COLOR_NODE_PICKED);
		Color nodePickedColor = new Color(rgb.red,rgb.green,rgb.blue);

		rgb = PreferenceConverter.getColor(store, PreferenceValues.NAME_COLOR_BACKGROUND);
		Color backgroundColor = new Color(rgb.red, rgb.green, rgb.blue);
		vv.setBackground(backgroundColor);

		vv.getRenderContext().setVertexFillPaintTransformer(new PickableVertexPaintTransformer<INode>(vv.getPickedVertexState(),
				nodeFillColor, nodePickedColor));

		//vv.getRenderContext().setEdgeShapeTransformer(new EdgeShape.Line<INode, IEdge>());

		
		if (prefs.getBoolean(PreferenceValues.NAME_ANNOTATED_EDGES,PreferenceValues.VALUE_ANNOTATED_EDGES_DEFAULT)){
			vv.getRenderContext().setEdgeLabelTransformer(new ToStringLabeller<IEdge>(){
				public String transform(IEdge edge){
					String edgeName = "";
					if (edge.getPayload() != null){
						edgeName = edge.getPayload().getName();
					}
					else
					{
						edgeName = edge.toString();
					}
					return edgeName;
				}
			});
		}

		//set preferred Graph Layout, default Layout = KKLayout
		String prefLayout = prefs.get(PreferenceValues.NAME_LAYOUT, PreferenceValues.VALUE_LAYOUT_DEFAULT);
		if (prefLayout.equalsIgnoreCase("TestLayout"))
		{
			layout = new TestLayout2(graph, rootNode);
		}
		//else{
			/*
			 * add back edges for all Layouts besides TestLayout	
			 */
//			if (!backEdges.isEmpty()){
//				for (IEdge backedge : backEdges){
//
//					//System.out.println( backedge.getSource() + " ----->"  +  backedge.getTarget());
//					graph.addEdge(backedge, backedge.getSource(), backedge.getTarget(),EdgeType.DIRECTED);
//				}
//			}

		else if (prefLayout.equalsIgnoreCase("FRLayout"))
		{
			layout = new FRLayout<INode,IEdge>(graph);
		}
		else if (prefLayout.equalsIgnoreCase("FRLayout2"))
		{
			layout = new FRLayout2<INode,IEdge>(graph);
		}
		else if (prefLayout.equalsIgnoreCase("ISOMLayout"))
		{
			layout = new ISOMLayout<INode,IEdge>(graph);
		}
		else if (prefLayout.equals("KKLayout"))
		{
			layout = new KKLayout<INode,IEdge>(graph);
			((KKLayout<INode, IEdge>) layout).setMaxIterations(400);
		}
		else 
		{
			MinimumSpanningForest2<INode,IEdge> prim = 
				new MinimumSpanningForest2<INode,IEdge>(graph,
						new DelegateForest<INode,IEdge>(), DelegateTree.<INode,IEdge>getFactory(),
						new ConstantTransformer(1.0));

			Forest<INode,IEdge> tree = prim.getForest();
			Layout<INode,IEdge> layout1 = new TreeLayout<INode, IEdge>(tree);
			layout = new StaticLayout<INode,IEdge>(graph, layout1);
		}
		this.vv = vv;
		vv.setGraphLayout(layout);
		
	}

}
