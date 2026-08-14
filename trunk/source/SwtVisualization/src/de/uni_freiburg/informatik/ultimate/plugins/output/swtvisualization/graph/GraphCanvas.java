/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE SwtVisualization plug-in.
 *
 * The ULTIMATE SwtVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SwtVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SwtVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SwtVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SwtVisualization plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.graph;

import java.util.Map;
import java.util.Set;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.MouseMoveListener;
import org.eclipse.swt.events.MouseWheelListener;
import org.eclipse.swt.events.PaintEvent;
import org.eclipse.swt.events.PaintListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Canvas;
import org.eclipse.swt.widgets.Composite;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.editor.SwtEditorInput;

/**
 * SWT Canvas that renders the graph (nodes as rounded rectangles, edges as lines with arrowheads) and handles
 * mouse interaction (node selection, panning, zooming).
 */
public class GraphCanvas extends Canvas {

	private static final int ARROW_SIZE = 10;
	private static final int ARC = 12;

	private SwtEditorInput mInput;
	private GraphLayout mLayout;
	private VisualizationNode mSelectedNode;

	// Pan & zoom state
	private double mTranslateX = 0;
	private double mTranslateY = 0;
	private double mZoom = 1.0;

	// Drag state
	private Point mDragStartPoint;
	private boolean mIsDragging;

	// Colors
	private Color mNodeColor;
	private Color mPickedColor;
	private Color mBackgroundColor;
	private Color mEdgeColor;
	private Color mCounterExampleColor;

	// Callback for selection changes
	private INodeSelectionListener mSelectionListener;

	/**
	 * Listener interface for node selection events.
	 */
	public interface INodeSelectionListener {
		void nodeSelected(IElement element);
	}

	public GraphCanvas(final Composite parent) {
		super(parent, SWT.DOUBLE_BUFFERED | SWT.BORDER);

		initColors();

		addPaintListener(new PaintListener() {
			@Override
			public void paintControl(final PaintEvent e) {
				onPaint(e);
			}
		});

		addMouseListener(new MouseListener() {
			@Override
			public void mouseUp(final MouseEvent e) {
				if (mIsDragging) {
					mIsDragging = false;
					setCursor(getDisplay().getSystemCursor(SWT.CURSOR_ARROW));
				}
				mDragStartPoint = null;
			}

			@Override
			public void mouseDown(final MouseEvent e) {
				if (e.button == 1) {
					// Left click: try node selection
					final VisualizationNode hit = hitTest(e.x, e.y);
					if (hit != null) {
						setSelectedNode(hit);
					} else {
						// Start panning
						mDragStartPoint = new Point(e.x, e.y);
						mIsDragging = true;
						setCursor(getDisplay().getSystemCursor(SWT.CURSOR_SIZEALL));
					}
				} else if (e.button == 2 || e.button == 3) {
					// Middle or right button: panning
					mDragStartPoint = new Point(e.x, e.y);
					mIsDragging = true;
					setCursor(getDisplay().getSystemCursor(SWT.CURSOR_SIZEALL));
				}
			}

			@Override
			public void mouseDoubleClick(final MouseEvent e) {
				// No-op for now
			}
		});

		addMouseMoveListener(new MouseMoveListener() {
			@Override
			public void mouseMove(final MouseEvent e) {
				if (mIsDragging && mDragStartPoint != null) {
					mTranslateX += e.x - mDragStartPoint.x;
					mTranslateY += e.y - mDragStartPoint.y;
					mDragStartPoint = new Point(e.x, e.y);
					redraw();
				}
			}
		});

		addMouseWheelListener(new MouseWheelListener() {
			@Override
			public void mouseScrolled(final MouseEvent e) {
				final double oldZoom = mZoom;
				if (e.count > 0) {
					mZoom = Math.min(mZoom * 1.1, 5.0);
				} else {
					mZoom = Math.max(mZoom / 1.1, 0.1);
				}
				// Zoom toward mouse position
				mTranslateX = e.x - (e.x - mTranslateX) * (mZoom / oldZoom);
				mTranslateY = e.y - (e.y - mTranslateY) * (mZoom / oldZoom);
				redraw();
			}
		});
	}

	private void initColors() {
		mNodeColor = new Color(getDisplay(), new RGB(180, 220, 255));
		mPickedColor = new Color(getDisplay(), new RGB(255, 235, 100));
		mBackgroundColor = new Color(getDisplay(), new RGB(255, 255, 255));
		mEdgeColor = new Color(getDisplay(), new RGB(0, 0, 0));
		mCounterExampleColor = new Color(getDisplay(), new RGB(255, 0, 0));
	}

	/**
	 * Set the graph data and trigger layout computation.
	 */
	public void setInput(final SwtEditorInput input) {
		mInput = input;
		if (input != null) {
			mLayout = GraphLayout.create("TreeLayout", input.getRootNode(), input.getNodes(), input.getEdges());
			mLayout.computeLayout(null);
		} else {
			mLayout = null;
		}
		mSelectedNode = null;
		redraw();
	}

	public void setSelectionListener(final INodeSelectionListener listener) {
		mSelectionListener = listener;
	}

	public void setSelectedNode(final VisualizationNode node) {
		mSelectedNode = node;
		redraw();
		if (mSelectionListener != null) {
			final Object backing = node.getBacking();
			if (backing instanceof IElement element) {
				mSelectionListener.nodeSelected(element);
			} else {
				// The VisualizationNode itself implements IElement
				mSelectionListener.nodeSelected(node);
			}
		}
	}

	public VisualizationNode getSelectedNode() {
		return mSelectedNode;
	}

	private void onPaint(final PaintEvent e) {
		final GC gc = e.gc;

		// Draw background
		gc.setBackground(mBackgroundColor);
		gc.fillRectangle(e.x, e.y, e.width, e.height);

		if (mLayout == null || mInput == null) {
			gc.drawString("No graph data", 10, 10);
			return;
		}

		// Apply zoom and translation
		gc.setAdvanced(true);
		gc.setTextAntialias(SWT.ON);
		gc.setAntialias(SWT.ON);

		// Save original transform values and apply our transformation manually
		final Map<VisualizationNode, NodeLayoutInfo> positions = mLayout.getNodePositions();
		final Set<VisualizationEdge> backEdges = mLayout.getBackEdges();

		// Draw edges first (so nodes are on top)
		for (final VisualizationEdge edge : mInput.getEdges()) {
			final NodeLayoutInfo sourceInfo = positions.get(edge.getSource());
			final NodeLayoutInfo targetInfo = positions.get(edge.getTarget());
			if (sourceInfo == null || targetInfo == null) {
				continue;
			}

			final int sx = transformX(sourceInfo.getX());
			final int sy = transformY(sourceInfo.getY());
			final int tx = transformX(targetInfo.getX());
			final int ty = transformY(targetInfo.getY());

			final boolean isCounterExample = mInput.isCounterExampleEdge(edge);
			gc.setForeground(isCounterExample ? mCounterExampleColor : mEdgeColor);
			gc.setLineWidth(isCounterExample ? 2 : 1);

			if (backEdges.contains(edge)) {
				// Draw back-edge as a curved line (simplified: use an offset)
				drawCurvedEdge(gc, sx, sy, tx, ty);
			} else {
				gc.drawLine(sx, sy, tx, ty);
			}

			// Draw arrowhead
			drawArrowhead(gc, sx, sy, tx, ty);
		}

		// Draw nodes
		for (final VisualizationNode node : mInput.getNodes()) {
			final NodeLayoutInfo info = positions.get(node);
			if (info == null) {
				continue;
			}
			final int x = transformX(info.getX() - info.getWidth() / 2.0);
			final int y = transformY(info.getY() - info.getHeight() / 2.0);
			final int w = (int) (info.getWidth() * mZoom);
			final int h = (int) (info.getHeight() * mZoom);

			final boolean selected = node.equals(mSelectedNode);
			gc.setBackground(selected ? mPickedColor : mNodeColor);
			gc.fillRoundRectangle(x, y, w, h, ARC, ARC);
			gc.setForeground(mEdgeColor);
			gc.setLineWidth(selected ? 2 : 1);
			gc.drawRoundRectangle(x, y, w, h, ARC, ARC);

			// Draw label
			final String label = getLabel(node);
			gc.setForeground(getDisplay().getSystemColor(SWT.COLOR_BLACK));
			final Point textExtent = gc.stringExtent(label);
			gc.drawString(label, x + (w - textExtent.x) / 2, y + (h - textExtent.y) / 2, true);
		}
	}

	private int transformX(final double x) {
		return (int) (x * mZoom + mTranslateX);
	}

	private int transformY(final double y) {
		return (int) (y * mZoom + mTranslateY);
	}

	private void drawArrowhead(final GC gc, final int sx, final int sy, final int tx, final int ty) {
		final double angle = Math.atan2(ty - sy, tx - sx);
		final int ax = (int) (tx - ARROW_SIZE * Math.cos(angle));
		final int ay = (int) (ty - ARROW_SIZE * Math.sin(angle));
		final int[] arrow = new int[6];
		arrow[0] = tx;
		arrow[1] = ty;
		arrow[2] = (int) (ax + ARROW_SIZE / 2.0 * Math.cos(angle + Math.PI / 2));
		arrow[3] = (int) (ay + ARROW_SIZE / 2.0 * Math.sin(angle + Math.PI / 2));
		arrow[4] = (int) (ax + ARROW_SIZE / 2.0 * Math.cos(angle - Math.PI / 2));
		arrow[5] = (int) (ay + ARROW_SIZE / 2.0 * Math.sin(angle - Math.PI / 2));
		gc.fillPolygon(arrow);
	}

	private void drawCurvedEdge(final GC gc, final int sx, final int sy, final int tx, final int ty) {
		// Draw a quadratic Bezier-like curve using two line segments
		final int midX = (sx + tx) / 2 + 30;
		final int midY = (sy + ty) / 2 - 30;
		gc.drawLine(sx, sy, midX, midY);
		gc.drawLine(midX, midY, tx, ty);
	}

	private static String getLabel(final VisualizationNode node) {
		final String s = node.toString();
		return s.length() > 30 ? s.substring(0, 30) : s;
	}

	/**
	 * Hit-test: find the node at the given canvas coordinates.
	 */
	private VisualizationNode hitTest(final int mx, final int my) {
		if (mLayout == null || mInput == null) {
			return null;
		}
		final Map<VisualizationNode, NodeLayoutInfo> positions = mLayout.getNodePositions();
		for (final VisualizationNode node : mInput.getNodes()) {
			final NodeLayoutInfo info = positions.get(node);
			if (info == null) {
				continue;
			}
			final int x = transformX(info.getX() - info.getWidth() / 2.0);
			final int y = transformY(info.getY() - info.getHeight() / 2.0);
			final int w = (int) (info.getWidth() * mZoom);
			final int h = (int) (info.getHeight() * mZoom);
			if (mx >= x && mx <= x + w && my >= y && my <= y + h) {
				return node;
			}
		}
		return null;
	}

	@Override
	public void dispose() {
		mNodeColor.dispose();
		mPickedColor.dispose();
		mBackgroundColor.dispose();
		mEdgeColor.dispose();
		mCounterExampleColor.dispose();
		super.dispose();
	}
}
