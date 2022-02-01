/*
 * Copyright (C) 2015 Laszlo Szathmary (jabba.laci@gmail.com)
 * Copyright (C) 2013-2015 Mostafa Mahmoud Amin
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CodeCheck plug-in.
 *
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission
 * to convey the resulting work.
 */
// GraphViz.java - a simple API to call dot from Java programs
/*
 ******************************************************************************
 *                                                                            *
 *              (c) Copyright 2003 Laszlo Szathmary                           *
 *                                                                            *
 * This program is free software; you can redistribute it and/or modify it    *
 * under the terms of the GNU Lesser General Public License as published by   *
 * the Free Software Foundation; either version 2.1 of the License, or        *
 * (at your option) any later version.                                        *
 *                                                                            *
 * This program is distributed in the hope that it will be useful, but        *
 * WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY *
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public    *
 * License for more details.                                                  *
 *                                                                            *
 * You should have received a copy of the GNU Lesser General Public License   *
 * along with this program; if not, write to the Free Software Foundation,    *
 * Inc., 675 Mass Ave, Cambridge, MA 02139, USA.                              *
 *                                                                            *
 ******************************************************************************
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * <dl>
 * <dt>Purpose: GraphViz Java API
 * <dd>
 * <dt>Description:
 * <dd>With this Java class you can simply call dot from your Java programs
 * <dt>Example usage:
 * <dd>
 *
 * <pre>
 * GraphViz gv = new GraphViz();
 * gv.addln(gv.start_graph());
 * gv.addln("A -> B;");
 * gv.addln("A -> C;");
 * gv.addln(gv.end_graph());
 * System.out.println(gv.getDotSource());
 *
 * String type = "gif";
 * File out = new File("out." + type); // out.gif in this example
 * gv.writeGraphToFile(gv.getGraph(gv.getDotSource(), type), out);
 * </pre>
 *
 * </dd>
 * </dl>
 *
 * @version v0.4, 2011/02/05 (February) -- Patch of Keheliya Gallaba is added. Now you can specify the type of the
 *          output file: gif, dot, fig, pdf, ps, svg, png, etc.
 * @version v0.3, 2010/11/29 (November) -- Windows support + ability to read the graph from a text file
 * @version v0.2, 2010/07/22 (July) -- bug fix
 * @version v0.1, 2003/12/04 (December) -- first release
 * @author Laszlo Szathmary (jabba.laci@gmail.com)
 */
public class GraphViz {
	public static final String END_GRAPH = "}";

	public static final String START_GRAPH = "digraph G {";

	/**
	 * The dir. where temporary files will be created.
	 */
	private static final String TEMP_DIR = System.getProperty("java.io.tmpdir");

	/**
	 * Where is your dot program located? It will be called externally.
	 */
	private static final String DOT = "c:/Program Files/GraphViz/bin/dot.exe";

	/**
	 * The source of the graph written in dot language.
	 */
	private StringBuilder mGraph;

	private final ILogger mLogger;

	/**
	 * Constructor
	 */
	public GraphViz(final ILogger logger) {
		mGraph = new StringBuilder();
		mLogger = logger;
	}

	/**
	 * Returns the graph's source description in dot language.
	 *
	 * @return Source of the graph in dot language.
	 */
	public String getDotSource() {
		return mGraph.toString();
	}

	/**
	 * Adds a string to the graph's source (without newline).
	 *
	 * @param line
	 *            the line to add.
	 */
	public void add(final String line) {
		mGraph.append(line);
	}

	/**
	 * Adds a string to the graph's source (with newline).
	 *
	 * @param line
	 *            the line to add.
	 */
	public void addLine(final String line) {
		mGraph.append(line).append(CoreUtil.getPlatformLineSeparator());
	}

	/**
	 * Adds a newline to the graph's source.
	 */
	public void addLine() {
		mGraph.append(CoreUtil.getPlatformLineSeparator());
	}

	/**
	 * Returns the graph as an image in binary format.
	 *
	 * @param dot_source
	 *            Source of the graph to be drawn.
	 * @param type
	 *            Type of the output image to be produced, e.g.: gif, dot, fig, pdf, ps, svg, png.
	 * @return A byte array containing the image of the graph.
	 */
	public byte[] getGraph(final String dot_source, final String type) {
		File dot;
		byte[] imgStream = new byte[0];

		dot = writeDotSourceToFile(dot_source);
		if (dot != null) {
			imgStream = getImgStream(dot, type);
			if (!dot.delete()) {
				mLogger.warn(dot.getAbsolutePath() + " could not be deleted!");
			}
		}
		return imgStream;
	}

	/**
	 * Writes the graph's image in a file.
	 *
	 * @param img
	 *            A byte array containing the image of the graph.
	 * @param file
	 *            Name of the file to where we want to write.
	 * @return Success: 1, Failure: -1
	 */
	public static int writeGraphToFile(final byte[] img, final String file) {
		final File to = new File(file);
		return writeGraphToFile(img, to);
	}

	/**
	 * Writes the graph's image in a file.
	 *
	 * @param img
	 *            A byte array containing the image of the graph.
	 * @param to
	 *            A File object to where we want to write.
	 * @return Success: 1, Failure: -1
	 */
	public static int writeGraphToFile(final byte[] img, final File to) {
		if (img == null || img.length == 0 || to == null) {
			return -1;
		}
		try (final FileOutputStream fos = new FileOutputStream(to)) {
			fos.write(img);
		} catch (final IOException ioe) {
			return -1;
		}
		return 1;
	}

	/**
	 * It will call the external dot program, and return the image in binary format.
	 *
	 * @param dot
	 *            Source of the graph (in dot language).
	 * @param type
	 *            Type of the output image to be produced, e.g.: gif, dot, fig, pdf, ps, svg, png.
	 * @return The image of the graph in .gif format.
	 */
	private byte[] getImgStream(final File dot, final String type) {
		try {
			final File img = File.createTempFile("graph_", "." + type, new File(GraphViz.TEMP_DIR));
			final Runtime rt = Runtime.getRuntime();

			// patch by Mike Chenault
			final String[] args = { DOT, "-T" + type, dot.getAbsolutePath(), "-o", img.getAbsolutePath() };
			final Process p = rt.exec(args);

			p.waitFor();

			byte[] imgStream = new byte[0];
			try (FileInputStream in = new FileInputStream(img.getAbsolutePath())) {
				imgStream = new byte[in.available()];
				final int readbytes = in.read(imgStream);
				if (readbytes != -1) {
					throw new IOException("Could not read to the end");
				}
			}
			if (!img.delete()) {
				mLogger.warn(img.getAbsolutePath() + " could not be deleted!");
			}
			return imgStream;
		} catch (final IOException ioe) {
			mLogger.error(
					"I/O processing of tempfile in dir " + GraphViz.TEMP_DIR + " failed. Message: " + ioe.getMessage());
			return new byte[0];
		} catch (final InterruptedException ie) {
			mLogger.error("The execution of the external program was interrupted: " + ie.getMessage());
			Thread.currentThread().interrupt();
			return new byte[0];
		}
	}

	/**
	 * Writes the source of the graph in a file, and returns the written file as a File object.
	 *
	 * @param str
	 *            Source of the graph (in dot language).
	 * @return The file (as a File object) that contains the source of the graph.
	 */
	private File writeDotSourceToFile(final String str) {
		File temp;
		try {
			temp = File.createTempFile("graph_", ".dot.tmp", new File(GraphViz.TEMP_DIR));
			CoreUtil.writeFile(temp, str);
		} catch (final IOException e) {
			mLogger.error("I/O error while writing the dot source to temp file: " + e.getMessage());
			return null;
		}
		return temp;
	}

	/**
	 * Read a DOT graph from a text file.
	 *
	 * @param input
	 *            Input text file containing the DOT graph source.
	 */
	public void readSource(final String input) {
		final StringBuilder sb = new StringBuilder();
		try {
			CoreUtil.readFileLineByLine(input, sb::append);
		} catch (final IOException e) {
			mLogger.error("Error: " + e.getMessage());
		}
		mGraph = sb;
	}
}
