/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.gui;

import java.awt.*;
import java.awt.event.*;
import java.util.*;
import java.util.regex.*;
import java.util.List;

import javax.swing.*;

//import de.uni_muenster.cs.sev.lethal.parser.tree.ParseException;
//import de.uni_muenster.cs.sev.lethal.parser.tree.TreeParser;
import de.uni_muenster.cs.sev.lethal.symbol.common.*;
import de.uni_muenster.cs.sev.lethal.symbol.special.Cons;
import de.uni_muenster.cs.sev.lethal.symbol.special.Nil;
import de.uni_muenster.cs.sev.lethal.tree.common.Tree;

/**
 * Display control to visualize a tree.<br>
 * Scroll and zoom are supported as well as different node shapes.
 * @author Philipp, Sezar
 *
 */
public class TreeViewer extends JPanel{
	private static final int STYLE_CIRCLE = 0;
	private static final int STYLE_OVAL = 1;
	private static final int STYLE_RECTANGLE = 2;
	private static final int STYLE_ROUND_RECTANGLE = 3;

	/**
	 * The Tree currently displayed by this TreeViewer.
	 */
	protected Tree<? extends Symbol> tree;

	private int style = STYLE_ROUND_RECTANGLE;
	private int subtreeDistY = 10;
	private int subtreeDistX = 5;
	private int minNodeSize = 30;
	private Color nodeColor = Color.YELLOW;
	private Color specialNodeColor = Color.ORANGE;
	private Color nodeHighlightColor = Color.BLUE;
	private Color textColor = Color.BLACK;
	private Color lineColor = Color.BLACK;

	private final int unrankedSymbolMarkSize = 6;

	private Font refFont = new Font("Monospaced", Font.BOLD, 16);
	private Font textFont = refFont;

	private Font annotationsRefFont = new Font("Monospaced",Font.PLAIN, 10);
	private Font annotationsFont = annotationsRefFont;	

	private float zoomFactor = 1;

	protected List<NodeInfo> nodeInfos;
	protected Map<Tree<? extends Symbol>,NodeAnnotation> nodeAnnotations;
	protected Dimension unscaledTreeSize;

	protected JToolBar toolbar = new JToolBar();
	protected JButton styleSelector = new JButton(Resources.loadIcon("style.png"));
	protected JComboBox zoomSelector = new JComboBox(new String[]{"20%", "25%", "50%", "75%", "100%", "125%", "150%", "200%"});
	protected JPanel paintBox;
	protected JScrollPane scrollBox;

	/**
	 * Creates a tree viewer control for a tree without annotations.
	 * @param tree the tree to show
	 */
	public TreeViewer(Tree<? extends Symbol> tree){
		this(tree, new HashMap<Tree<? extends Symbol>,NodeAnnotation>());
	}

	/**
	 * Creates a tree viewer control for a tree with annotations.
	 * @param tree the tree to show
	 * @param nodeAnnotations annotations for the (sub)trees
	 */
	public TreeViewer(Tree<? extends Symbol> tree, Map<Tree<? extends Symbol>,NodeAnnotation> nodeAnnotations){
		this.tree = tree;
		this.nodeAnnotations = nodeAnnotations;
		this.setLayout(new BorderLayout());
		this.add(this.toolbar, BorderLayout.NORTH);

		JButton b = new JButton(Resources.loadIcon("zoom-out.png"));
		b.setToolTipText("Zoom in");
		if (b.getIcon() == null) b.setText(b.getToolTipText());
		b.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) { setZoomFactor(getZoomFactor() - 0.10F); }
		});
		this.toolbar.add(b);

		//this.toolbar.add(new JLabel("Zoom:"));
		this.toolbar.add(this.zoomSelector);
		this.zoomSelector.setEditable(true);
		this.zoomSelector.setSelectedItem("100%");
		this.zoomSelector.setPreferredSize(this.zoomSelector.getMinimumSize());
		this.zoomSelector.setSize(this.zoomSelector.getMinimumSize());
		this.zoomSelector.addItemListener(new ItemListener(){
			@Override
			public void itemStateChanged(ItemEvent e) {
				if (e.getStateChange() == ItemEvent.SELECTED){
					Float zoom = parsePrecent((String)e.getItem());
					if (zoom != null){
						TreeViewer.this.setZoomFactor(zoom);
					} else {
						TreeViewer.this.zoomSelector.setSelectedItem(toPercentString(TreeViewer.this.getZoomFactor()));
					}
				}
			}
		});

		b = new JButton(Resources.loadIcon("zoom-fit-best.png"));
		b.setToolTipText("Best fit");
		b.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) { autoZoom(0.2F,2F); }
		});
		this.toolbar.add(b);

		/*b = new JButton(Resources.loadIcon("zoom-original.png"));
		b.setToolTipText("Zoom 100%");
		b.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) { setZoomFactor(1); }
		});
		this.toolbar.add(b);*/

		b = new JButton(Resources.loadIcon("zoom-in.png"));
		b.setToolTipText("Zoom in");
		if (b.getIcon() == null) b.setText(b.getToolTipText());
		b.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) { setZoomFactor(getZoomFactor() + 0.10F); }
		});
		this.toolbar.add(b);

		this.toolbar.addSeparator();

		this.toolbar.add(styleSelector);
		this.styleSelector.setToolTipText("Node Shape");


		this.paintBox = new JPanel(){
			@Override public void paintComponent(Graphics g) { paintTree(this, g);}

			/**
			 * @see javax.swing.JComponent#getToolTipText(java.awt.event.MouseEvent)
			 */
			@Override
			public String getToolTipText(MouseEvent event) {
				if (TreeViewer.this.nodeInfos == null || TreeViewer.this.nodeInfos.size() == 0) return null;
				if (TreeViewer.this.nodeAnnotations == null || TreeViewer.this.nodeAnnotations.size() == 0) return null;
				Point p = event.getPoint();
				for (NodeInfo n : nodeInfos){
					if (n.rect.contains(p)){
						NodeAnnotation ann = TreeViewer.this.nodeAnnotations.get(n.tree);
						return (ann == null) ? null : ann.tooltip;
					}
				}
				return null;
			}
			
		};
		
		this.paintBox.setToolTipText("foo");
		
		this.scrollBox = new JScrollPane(this.paintBox);
		this.add(this.scrollBox, BorderLayout.CENTER);

		this.styleSelector.addActionListener(new ActionListener(){
			@Override
			public void actionPerformed(ActionEvent e) {
				final List<String> styles = Arrays.asList("Circle", "Oval","Rectangle", "Round Rectangle");

				ActionListener l = new ActionListener(){
					public void actionPerformed(ActionEvent e) {
						TreeViewer.this.setStyle(styles.indexOf( ((JMenuItem)e.getSource()).getText() ));
					}
				};

				JPopupMenu menu = new JPopupMenu();
				for (int i = 0; i < styles.size(); i++){
					JMenuItem item = new JRadioButtonMenuItem(styles.get(i), TreeViewer.this.style == i);
					item.addActionListener(l);
					menu.add(item);
				}
				menu.show(TreeViewer.this.styleSelector, 0, TreeViewer.this.styleSelector.getHeight());
			}
		});
	}

	/**
	 * Paints the current tree to the given component and graphics.
	 * @param comp tree display component
	 * @param g graphics to paint to
	 */
	public void paintTree(JComponent comp, Graphics g) {
		if (nodeInfos == null) calcNodeInfos(g,TreeViewer.this.tree); //no node info's about the current tree, calculate them.

		g.clearRect(0,0,comp.getWidth(), comp.getHeight());

		if (g instanceof Graphics2D){
			((Graphics2D)g).setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
		}

		Dimension size = new Dimension(0,0);
		if (this.tree != null){
			g.setFont(this.textFont);

			for (NodeInfo node : this.nodeInfos){
				paintNode(g, node);
				NodeInfo parent = node.parent;
				if (parent != null){ 
					g.setColor(this.lineColor);
					g.drawLine(map(node.rect.x + node.rect.width / 2), map(node.rect.y),
							map(parent.rect.x + parent.rect.width / 2) , map(parent.rect.y + parent.rect.height));
				}
				size.height = Math.max(size.height, node.rect.y + node.rect.height);
				size.width = Math.max(size.width, node.rect.x + node.rect.width);
			}

			//g.drawRect(0,0, size.width, size.height);
		}
		this.unscaledTreeSize = size;

		updatePanelSize();
	}

	/**
	 * Calculates position, text, and annotations for all nodes in the given tree.<br>
	 * The position is the upper left corner of the rectangle containing the tree.
	 * The paint rectangle size is dynamically determined by the tree structure.
	 * @param g graphics to paint to
	 * @param tree tree to paint
	 */
	protected void calcNodeInfos(Graphics g, Tree<? extends Symbol> tree){
		this.nodeInfos = new ArrayList<NodeInfo>();
		if (tree != null) calcNodeInfos(g ,tree, null, 0, this.nodeInfos,new Point(0,0), 0);
	}

	/**
	 * Calculates position, text, and annotations for all nodes in the given tree.<br>
	 * The position is the upper left corner of the rectangle containing the tree.
	 * The paint rectangle size is dynamically determined by the tree structure.
	 * @param g graphics to paint to
	 * @param tree tree to paint
	 * @param childIndex TODO
	 * @param pos upper left corner of the area where the tree will be painted
	 * @param subtreePadding additional horizontal space between the left border 
	 * of the tree and the subtrees (used for centering small subtrees below big root nodes)
	 * @return the area the tree occupies
	 */
	private TreeArea calcNodeInfos(Graphics g, Tree<? extends Symbol> tree, NodeInfo parentInfo, int childIndex, List<NodeInfo> nodeInfos, Point pos, int subtreePadding){
		Dimension rootNodeSize = getNodeSize(g, tree);
		int subtreeHeight = 0;

		NodeInfo nodeInfo = new NodeInfo(tree, parentInfo, childIndex);

		if (tree.getSubTrees().size() != 0){
			List<NodeInfo> subtreeChildrenInfos = new ArrayList<NodeInfo>();

			//draw subtrees, collect occupied areas
			ArrayList<TreeArea> childAreas = new ArrayList<TreeArea>(tree.getSubTrees().size());
			Point childPos = new Point(pos.x+ subtreePadding, pos.y + rootNodeSize.height + subtreeDistY);
			int i = 0;
			for (Tree<? extends Symbol> subtree : tree.getSubTrees()){
				TreeArea childArea = calcNodeInfos(g, subtree, nodeInfo, i, subtreeChildrenInfos, childPos, 0);
				childPos.x = childArea.treeRect.x + childArea.treeRect.width + subtreeDistX;  //next child goes on the right edge of the previous one.
				childAreas.add(childArea);
				subtreeHeight = Math.max(subtreeHeight, childArea.treeRect.height);
				i++;
			}
			TreeArea firstChildArea = childAreas.get(0);
			TreeArea lastChildArea = childAreas.get(childAreas.size()-1);

			//Width of the subtrees (from left edge of the fist subtree to right edge of the last subtree); 
			int subtreeWidth = lastChildArea.treeRect.x + lastChildArea.treeRect.width - firstChildArea.treeRect.x;

			//Space between the centers of the first and last subtree root nodes (first and last child nodes). Math.max() in case the root node is wider than the subtrees
			int rootNodeSpaceWidth =  (lastChildArea.rootRect.x + (lastChildArea.rootRect.width / 2))
			- (firstChildArea.rootRect.x + (firstChildArea.rootRect.width / 2));

			//x pos of the root node
			int rootNodeLeft = firstChildArea.rootRect.x + (firstChildArea.rootRect.width / 2) + ((rootNodeSpaceWidth - rootNodeSize.width) / 2);
			if (rootNodeLeft < pos.x) { //problem, the subtrees are too small for the node to be centered above them without being moved too far to the left. Move the tree to the right and try again.
				g.clearRect(map(firstChildArea.treeRect.x), map(firstChildArea.treeRect.y), map(subtreeWidth), map(subtreeHeight));
				return calcNodeInfos(g, tree, parentInfo,childIndex, nodeInfos, pos, subtreePadding + (pos.x - rootNodeLeft));
			}

			//tree width is the rightmost point or either root node or last child minus the x pos of this tree.
			int treeWidth = Math.max(lastChildArea.treeRect.x + lastChildArea.treeRect.width, rootNodeLeft + rootNodeSize.width) - pos.x;

			//draw rectangle of the root node
			Rectangle rootRect = new Rectangle(rootNodeLeft, pos.y, rootNodeSize.width, rootNodeSize.height);

			//save info for painting
			nodeInfo.rect = rootRect;
			nodeInfos.add(nodeInfo);
			nodeInfos.addAll(subtreeChildrenInfos);

			return new TreeArea(
					rootRect,
					new Rectangle(pos.x, pos.y, treeWidth, rootNodeSize.height+ subtreeDistY + subtreeHeight));
		} else {
			Rectangle rootRect = new Rectangle(pos, rootNodeSize);
			nodeInfo.rect = rootRect;
			nodeInfos.add(nodeInfo);
			return new TreeArea(rootRect, rootRect);
		}
	}

	/**
	 * Calculates the size of the root node of the given tree when painted.
	 * This method does NOT actually paint anything.
	 * @param g graphics the node would be painted to
	 * @param tree the subtrees who's root node should be painted
	 * @return the size of the root node of the given tree in pixels
	 */
	private Dimension getNodeSize(Graphics g, Tree<? extends Symbol> tree){
		g.setFont(refFont);
		NodeAnnotation annotation = this.nodeAnnotations.get(tree);
		Object content = null;
		//if (tree.getSymbol() instanceof ContentSymbol<?>) content = ((ContentSymbol<?>)tree.getSymbol()).getContent();
		if (tree.getSymbol() instanceof RankedSymbol) content = String.valueOf(((RankedSymbol)tree.getSymbol()).getArity());

		g.setFont(refFont);
		String name = (tree.getSymbol() instanceof NamedSymbol<?>) ? ((NamedSymbol<?>)tree.getSymbol()).getName().toString() : tree.getSymbol().toString();
		int wNode = g.getFontMetrics().stringWidth(name);

		int wAnnotation = 0;
		if(annotation != null){
			g.setFont(this.annotationsFont);
			wAnnotation = g.getFontMetrics().stringWidth(annotation.text);
		}

		int wContent = 0;
		if (content != null){
			String s = content.toString();
			g.setFont(this.annotationsFont);
			wContent = g.getFontMetrics().stringWidth(s);
		}

		int w = Math.max(wContent, Math.max(wAnnotation, wNode));

		if(w < minNodeSize) w = minNodeSize;

		switch  (style){
		case STYLE_CIRCLE:
			return new Dimension(w, w);
		case STYLE_OVAL:
		case STYLE_RECTANGLE:
		case STYLE_ROUND_RECTANGLE:
			g.setFont(refFont);
			int hName = g.getFontMetrics().getHeight();
			g.setFont(this.annotationsFont);
			int hAnnotation = (annotation != null) ? g.getFontMetrics().getHeight() : 0;
			int hContent = (content != null) ? g.getFontMetrics().getHeight() : 0;
			int h = hName + hAnnotation + hContent;

			if(h < minNodeSize) h = minNodeSize;

			return new Dimension(w, h);

		default:
			return null;
		}
	}

	/**
	 * Paints a node to the given graphics object.
	 * @param g graphics to paint to
	 * @param node node to paint
	 */
	private void paintNode(Graphics g, NodeInfo node){
		NodeAnnotation annotation = this.nodeAnnotations.get(node.tree);
		String name = (node.tree.getSymbol() instanceof NamedSymbol<?>) ? ((NamedSymbol<?>)node.tree.getSymbol()).getName().toString() : node.tree.getSymbol().toString();
		boolean special = node.tree.getSymbol().equals(Nil.getNil()) || node.tree.getSymbol().equals(Cons.getCons());
		Object content = null;
		//if (node.tree.getSymbol() instanceof ContentSymbol<?>){
		//	content = ((ContentSymbol<?>)node.tree.getSymbol()).getContent();
		//}
		if (tree.getSymbol() instanceof RankedSymbol) content = String.valueOf(((RankedSymbol)node.tree.getSymbol()).getArity());

		g.setFont(this.textFont);
		int hName = g.getFontMetrics().getHeight();
		g.setFont(this.annotationsFont);
		int hAnnotation = (annotation != null) ? g.getFontMetrics().getHeight() : 0 ;
		int hContent = (content != null) ? g.getFontMetrics().getHeight() : 0; 
		int hText = hName + hAnnotation + hContent;


		if (annotation != null && annotation.highlight){
			g.setColor(this.nodeHighlightColor);
		} else if (special) {
			g.setColor(this.specialNodeColor);
		} else {
			g.setColor(this.nodeColor);
		}
		switch (style){
		case STYLE_CIRCLE:
		case STYLE_OVAL:
			g.fillOval(map(node.rect.x), map(node.rect.y), map(node.rect.width), map(node.rect.height));
			break;
		case STYLE_RECTANGLE:
			g.fillRect(map(node.rect.x), map(node.rect.y), map(node.rect.width), map(node.rect.height));
			break;
		case STYLE_ROUND_RECTANGLE:
			g.fillRoundRect(map(node.rect.x), map(node.rect.y), map(node.rect.width), map(node.rect.height),map(15),map(15));
		}


		if (!(node.tree.getSymbol() instanceof RankedSymbol)){
			g.setColor(this.lineColor);
			g.fillOval(map(node.rect.x + (node.rect.width / 2) - unrankedSymbolMarkSize/2), map(node.rect.y + node.rect.height - unrankedSymbolMarkSize/2), map(unrankedSymbolMarkSize), map(unrankedSymbolMarkSize));
		}

		int w;
		int texty = map(node.rect.y) + (map(node.rect.height) - hText)/2;

		if (annotation != null){
			if (hAnnotation >= 8){
				g.setColor(this.textColor);
				g.setFont(this.annotationsFont);

				w = g.getFontMetrics().stringWidth(annotation.text);
				switch  (style){
				case STYLE_CIRCLE:
				case STYLE_OVAL:
					g.drawString(annotation.text, (map(node.rect.x + node.rect.width/2)-w/2), texty+(int)(hAnnotation*0.7));
					break;
				case STYLE_RECTANGLE:
				case STYLE_ROUND_RECTANGLE:	
					g.drawString(annotation.text, map(node.rect.x + node.rect.width)- w, texty+(int)(hAnnotation*0.7));
					break;
				}
				texty += hAnnotation;
			}
		}

		if (hName >= 8) {
			g.setColor(this.textColor);
			g.setFont(this.textFont);

			w = g.getFontMetrics().stringWidth(name);

			g.drawString(name, map(node.rect.x)+(map(node.rect.width)-w)/2 , (texty+(int)(hName*0.7)));
			texty += hName;
		}

		if (content != null) {
			if (hContent >= 8){
				g.setColor(this.textColor);
				g.setFont(this.annotationsFont);

				String s = content.toString();
				w = g.getFontMetrics().stringWidth(s);
				g.drawString(s, (map(node.rect.x + node.rect.width/2)-w/2), texty+(int)(hContent*0.7));
			}
		}
	}

	private void updatePanelSize(){
		//scale the tree size according to the zoom factor
		Dimension size = new Dimension(map(this.unscaledTreeSize.width), map(this.unscaledTreeSize.height));

		if (!(paintBox.getPreferredSize().equals(size))){
			paintBox.setPreferredSize(size);
			paintBox.setSize(size); //need to set size to notify parent scroll pane
			if (this.toolbar.isVisible()){
				size = new Dimension(size.width, size.height + this.toolbar.getHeight());
			}
			this.setPreferredSize(size);
		}
	}

	/**
	 * Applies currently set zoom factor to a position or size.
	 * @param pos position to zoom
	 * @return TODO
	 */
	private int map(int pos){
		return (int)(pos * zoomFactor); 
	}

	private Float parsePrecent(String s){
		Pattern p = Pattern.compile("^\\s*(\\d+(?:.\\d+)?)\\s*(%)?\\s*$");
		Matcher m = p.matcher(s);
		if (!m.matches()) return null;
		Float f = Float.parseFloat(m.group(1));
		f /= 100.0F;
		return f;
	}
	private String toPercentString(Float f){
		float p = Math.round(f * 10000)/100.0F;
		if (p == Math.round(p)){
			return ((int)p)+"%";
		} else {
			return p+"%";
		}
	}

	/**
	 * Returns the tree node draw style.
	 * @return the tree node draw style
	 */
	public int getStyle() {
		return style;
	}

	/**
	 * Sets the tree node draw style.<br>
	 * Valid values are: STYLE_CIRCLE, STYLE_OVAL, STYLE_RECTANGLE, STYLE_ROUND_RECTANGLE.
	 * @param style the new tree node draw style
	 */
	public void setStyle(int style) {
		if (this.style != style){
			this.style = style;
			this.nodeInfos = null;
			this.repaint();
		}
	}

	/**
	 * Returns the vertical distance between tree nodes.
	 * @return the vertical distance between tree nodes
	 */
	public int getSubtreeDistY() {
		return subtreeDistY;
	}

	/**
	 * Sets the vertical distance between tree nodes.
	 * @param subtreeDistY the new vertical distance between tree nodes
	 */
	public void setSubtreeDistY(int subtreeDistY) {
		this.subtreeDistY = subtreeDistY;
		this.nodeInfos = null;
		this.repaint();
	}

	/**
	 * Returns the horizontal distance between tree nodes.
	 * @return the horizontal distance between tree nodes
	 */
	public int getSubtreeDistX() {
		return subtreeDistX;
	}

	/**
	 * Sets the horizontal distance between tree nodes.
	 * @param subtreeDistX the new horizontal distance between tree nodes
	 */
	public void setSubtreeDistX(int subtreeDistX) {
		this.subtreeDistX = subtreeDistX;
		this.nodeInfos = null;
		this.repaint();
	}

	/**
	 * Returns the minimal size of tree nodes.
	 * @return the minimal size of tree nodes
	 */
	public int getMinNodeSize() {
		return minNodeSize;
	}

	/**
	 * Sets the minimal size of the tree nodes.
	 * @param minNodeSize the new minimal size of the tree nodes
	 */
	public void setMinNodeSize(int minNodeSize) {
		this.minNodeSize = minNodeSize;
		this.nodeInfos = null;
		this.repaint();
	}


	/**
	 * Returns the normal (non-highlight) color of the tree nodes.
	 * @return the normal (non-highlight) color of the tree nodes
	 */
	public Color getNodeColor() {
		return nodeColor;
	}

	/**
	 * Sets the normal (non-highlight) color of the tree nodes.
	 * @param nodeColor The new normal (non-highlight) color of the tree nodes
	 */
	public void setNodeColor(Color nodeColor) {
		this.nodeColor = nodeColor;
	}


	/**
	 * Returns the text color.
	 * @return  the text color
	 */
	public Color getTextColor() {
		return textColor;
	}

	/**
	 * Sets the text color.
	 * @param textColor the new text color
	 */
	public void setTextColor(Color textColor) {
		this.textColor = textColor;
	}

	/**
	 * Returns the line color.
	 * @return the line color
	 */
	public Color getLineColor() {
		return lineColor;
	}
	
	/**
	 * Sets the line color.
	 * @param lineColor the new line color
	 */
	public void setLineColor(Color lineColor) {
		this.lineColor = lineColor;
	}

	@Override
	public Font getFont() {
		return refFont;
	}

	@Override
	public void setFont(Font refFont) {
		this.refFont = refFont;
	}

	/**
	 * Returns if the toolbar in the TreeViewer is visible.
	 * @return true if the toolbar is visible, false if not
	 */
	public boolean getToolbarVisible(){
		return this.toolbar.isVisible();
	}

	/**
	 * Sets the visibility of the toolbar in the TreeViewer control.
	 * @param visible the new visibility of the toolbar
	 */
	public void setToolbarVisible(boolean visible){
		this.toolbar.setVisible(visible);
	}

	/**
	 * Sets if ScrollBars should be shown if the tree size exceed the TreeViewer size.
	 * @param scroll true if they should be shown on demand, false of not
	 */
	public void setScrollEnabled(boolean scroll){
		this.scrollBox.setVerticalScrollBarPolicy(scroll ? ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED : ScrollPaneConstants.VERTICAL_SCROLLBAR_NEVER);
		this.scrollBox.setHorizontalScrollBarPolicy(scroll ? ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED : ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
	}

	/**
	 * Returns the current zoom factor.
	 * @return the current zoom factor
	 */
	public float getZoomFactor() {
		return zoomFactor;
	}

	/**
	 * Sets the zoom factor of the tree shown.
	 * @param zoomFactor the new tree zoom factor
	 */
	public void setZoomFactor(float zoomFactor) {
		if (this.zoomFactor != zoomFactor && zoomFactor > 0){
			this.zoomFactor = zoomFactor;
			this.textFont = new Font(this.refFont.getName(), this.refFont.getStyle(), (int)(this.refFont.getSize() * zoomFactor));
			this.annotationsFont = new Font(this.annotationsRefFont.getName(), this.annotationsRefFont.getStyle(), (int)(this.annotationsRefFont.getSize() * zoomFactor));
			this.zoomSelector.setSelectedItem(toPercentString(this.zoomFactor));
			this.repaint();
		}
	}

	/**
	 * Automatically adjust the zoom factor to make the tree fit the TreeViewer size.
	 * @param minFactor minimum zoom factor allowed
	 * @param maxFactor maximum zoom factor allowed
	 */
	public void autoZoom(float minFactor, float maxFactor){
		if (this.tree == null) return;
		if (this.nodeInfos == null) { this.calcNodeInfos(this.paintBox.getGraphics(), this.tree); updatePanelSize();}

		float h = this.getHeight() - 4; // HACK: XXX: 4 pixels are somewhere used for borders or so, don't know how to get the inner size.
		float w = this.getWidth() - 4;
		if (this.toolbar.isVisible()) h -= this.toolbar.getHeight();

		float zoom = Math.min(w / this.unscaledTreeSize.width,
				h / this.unscaledTreeSize.height);
		if (zoom < minFactor) zoom = minFactor;
		if (zoom > maxFactor) zoom = maxFactor;
		setZoomFactor(zoom);
	}

	/**
	 * Returns the tree currently display.
	 * @return the tree currently display
	 */
	public Tree<? extends Symbol> getTree() {
		return tree;
	}

	/**
	 * Sets the tree to show.
	 * @param tree the new tree to show. Null is allowed and will clear the display.
	 */
	public void setTree(Tree<? extends Symbol> tree){
		this.tree = tree;
		this.nodeInfos = null; //new tree, discard old calculated node infos 
		this.repaint();
	}	

	class TreeArea{
		Rectangle rootRect;
		Rectangle treeRect;
		public TreeArea(Rectangle rootRect, Rectangle treeRect) {
			this.rootRect = rootRect;
			this.treeRect = treeRect;
		}
	}
}

class NodeInfo{
	public Rectangle rect;

	public Tree<? extends Symbol> tree;
	public NodeInfo parent;
	public int childIndex;

	public NodeInfo(Tree<? extends Symbol> tree, NodeInfo parent, int childIndex) {
		this.tree = tree;
		this.parent = parent;
		this.childIndex = childIndex;
	}
	public NodeInfo(Tree<? extends Symbol> tree, Rectangle rect, NodeInfo parent, int childIndex) {
		this.tree = tree;
		this.rect = rect;
		this.parent = parent;
		this.childIndex = childIndex;
	}
}

class NodeAnnotation{
	String text;
	String tooltip;
	boolean highlight;
	public NodeAnnotation(String text, boolean highlight) {
		this.text = text;
		this.highlight = highlight;
	}
	public NodeAnnotation(String text, String tooltip, boolean highlight) {
		this.text = text;
		this.tooltip = tooltip;
		this.highlight = highlight;
	}
}
