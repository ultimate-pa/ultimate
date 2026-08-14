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

/**
 * Stores layout information (position and size) for a single node in the graph.
 */
public class NodeLayoutInfo {
	private double mX;
	private double mY;
	private int mWidth;
	private int mHeight;

	public NodeLayoutInfo(final double x, final double y, final int width, final int height) {
		mX = x;
		mY = y;
		mWidth = width;
		mHeight = height;
	}

	public double getX() {
		return mX;
	}

	public double getY() {
		return mY;
	}

	public int getWidth() {
		return mWidth;
	}

	public int getHeight() {
		return mHeight;
	}

	public void setX(final double x) {
		mX = x;
	}

	public void setY(final double y) {
		mY = y;
	}

	public void setWidth(final int width) {
		mWidth = width;
	}

	public void setHeight(final int height) {
		mHeight = height;
	}
}
