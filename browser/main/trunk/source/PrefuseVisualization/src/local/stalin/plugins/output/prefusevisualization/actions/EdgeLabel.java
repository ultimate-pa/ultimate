package local.stalin.plugins.output.prefusevisualization.actions;

import java.awt.geom.Rectangle2D;
import java.util.Iterator;

import local.stalin.plugins.output.prefusevisualization.gui.PrefuseColorSelection;
import local.stalin.plugins.output.prefusevisualization.gui.PrefuseFontSelection;

import prefuse.action.layout.Layout;
import prefuse.data.Schema;
import prefuse.util.FontLib;
import prefuse.util.PrefuseLib;
import prefuse.visual.DecoratorItem;
import prefuse.visual.VisualItem;

/**
 * Set label positions. Labels are assumed to be DecoratorItem instances,
 * decorating their respective nodes. The layout simply gets the bounds of the
 * decorated node and assigns the label coordinates to the center of those
 * bounds.
 * 
 * @author keil
 * @version 0.0.1 
 * $LastChangedDate: 2008-03-07 13:50:06 +0100 (Fr, 07 Mrz 2008) $
 * $LastChangedBy: keilr $
 * $LastChangedRevision: 495 $
 */
/**
 * @author Matthias
 *
 */
public class EdgeLabel extends Layout {

	private static PrefuseFontSelection prefuseFontSelection = new PrefuseFontSelection();
	private static PrefuseColorSelection prefuseColorSelection = new PrefuseColorSelection();
	
	/**
	 * DECORATOR_SCHEMA for the EdgeLabels, sets the Color and Font Value.
	 */
	private static Schema DECORATOR_SCHEMA = PrefuseLib
			.getVisualItemSchema();
	static {
		DECORATOR_SCHEMA.setDefault(VisualItem.INTERACTIVE, false);
		DECORATOR_SCHEMA.setDefault(VisualItem.TEXTCOLOR, prefuseColorSelection
				.getEdgeStyleColor());
		DECORATOR_SCHEMA.setDefault(VisualItem.FILLCOLOR, prefuseColorSelection
				.getEdgeStyleColor());
		DECORATOR_SCHEMA.setDefault(VisualItem.FONT, FontLib.getFont(prefuseFontSelection
				.getNodeFont().getFontName(), prefuseFontSelection.getNodeFont().getSize()-1 ));
	}

	/**
	 * @return the set DECORATOR_SCHEMA
	 */
	public static Schema getDecorator() {
		return DECORATOR_SCHEMA;
	}
	
	/**
	 * @param schema the new scheme
	 */
	public static void setDecorator(Schema schema) {
		EdgeLabel.DECORATOR_SCHEMA = schema;
	}

	public EdgeLabel(String group) {
		super(group);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see prefuse.action.GroupAction#run(double)
	 */
	public void run(double frac) {

		Iterator<?> iter = m_vis.items("name");
		while (iter.hasNext()) {
			DecoratorItem decorator = (DecoratorItem) iter.next();
						
			VisualItem decoratedItem = decorator.getDecoratedItem();
			Rectangle2D bounds = decoratedItem.getBounds();

			double x = bounds.getCenterX();
			double y = bounds.getCenterY();

			setX(decorator, null, x);
			setY(decorator, null, y);
		}
	}
}