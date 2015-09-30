/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie;

import java.io.IOException;

import org.apache.log4j.Logger;
import org.joogie.boogie.BoogieProgram;
import org.joogie.runners.SootRunner;
import org.joogie.runners.receivers.Receiver;

/**
 * Dispatcher.
 * 
 * @author arlt
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public final class Dispatcher {

	private final String mInput;
	private final SootRunner mSootRunner;
	private final HeapMode mHeapMode;
	private final String mScope;
	private final String mClasspath;
	private final Logger mLogger;

	/**
	 * Create a dispatcher to run the java-to-soot-to-boogie transformation of
	 * Joogie.
	 * 
	 * We use the current JRE as source for Java jars.
	 * 
	 * @param input
	 *            The path to a single input file (.java or .jar, .apk soonish).
	 * @param mode
	 *            The heap mode (as per Joogie spec)
	 * @param scope
	 *            A scope that can be used to exclude parts of the input from
	 *            the translation / analysis. May be null.
	 * @param classPath
	 *            Additions to the classpath in the soot format. May be null.
	 * @param logger
	 *            A logger instance that will be used throughout the run.
	 */
	public Dispatcher(final String input, final HeapMode mode, final String scope, final String classPath,
			final Logger logger) {
		mLogger = logger;
		mInput = input;
		mHeapMode = mode;
		mScope = scope;
		mClasspath = classPath;
		mSootRunner = new SootRunner(mLogger);
	}

	public BoogieProgram run() throws IOException {
		mLogger.debug("Running Soot: Java Bytecode to Boogie representation");
		final StringBuilder sootOutput = new StringBuilder();
		final Receiver receiver = new Receiver() {

			@Override
			public void receive(String text) {
				sootOutput.append(text);
			}

			@Override
			public void onEnd() {

			}

			@Override
			public void onBegin() {

			}
		};
		mSootRunner.addReceiver(receiver);
		final BoogieProgram prog = runSoot();
		mSootRunner.clearReceivers();
		mLogger.debug("Done");
		mLogger.info("Soot output:");
		mLogger.info(sootOutput);
		return prog;
	}

	private BoogieProgram runSoot() throws IOException {
		if (mInput.endsWith(".jar")) {
			// run with JAR file
			return mSootRunner.runWithJar(mInput, mClasspath, mScope, mHeapMode);
		} else if (mInput.endsWith(".java")) {
			// run with Source file
			return mSootRunner.runWithSource(mInput, mClasspath, mHeapMode, mScope);
		} else {
			// run with class file
			return mSootRunner.runWithClass(mInput, mClasspath, mHeapMode, mScope);
		}
	}
}
