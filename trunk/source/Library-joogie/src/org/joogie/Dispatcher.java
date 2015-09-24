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

import org.joogie.runners.SootRunner;
import org.joogie.util.Log;

/**
 * Dispatcher
 * 
 * @author arlt
 */
public final class Dispatcher {

	private final String mInput;
	private final String mSourceFolder;
	private final String mOutput;
	private final SootRunner mSootRunner;
	private final HeapMode mHeapMode;
	private final String mScope;
	private final String mClasspath;

	public Dispatcher(final String input, final String sourceFolder, final String output, final HeapMode mode,
			String scope, String classPath) {
		mInput = input;
		mSourceFolder = sourceFolder;
		mOutput = output;
		mSootRunner = new SootRunner();
		mHeapMode = mode;
		mScope = scope;
		mClasspath = classPath;
	}

	public void run() {
		try {
			Log.debug("Running Soot: Java Bytecode to Boogie representation");
			runSoot();
			Log.debug("Done");
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	private void runSoot() {
		if (mInput.endsWith(".jar")) {
			// run with JAR file
			mSootRunner.runWithJar(mInput, mClasspath, mScope, mOutput, mHeapMode);
		} else if (mInput.endsWith(".java")) {
			// run with Source file
			mSootRunner.runWithSource(mInput, mClasspath, mOutput, mHeapMode, mScope);
		} else {
			// run with class file
			mSootRunner.runWithClass(mInput, mSourceFolder, mOutput, mHeapMode, mScope);
		}
	}

	public SootRunner getSootRunner() {
		return mSootRunner;
	}
}
