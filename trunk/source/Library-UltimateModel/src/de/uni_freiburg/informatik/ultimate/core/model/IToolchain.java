/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.model;

import java.io.File;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;

/**
 *
 * TODO: Comments !
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IToolchain<T> {

	/**
	 * (Re)-initializes the plugins, the memory manager, and the benchmark. This should be called before calling
	 * {@link #processToolchain(IProgressMonitor)}.
	 *
	 * <b> Has to be called first</b>
	 */
	void init(IToolchainProgressMonitor monitor);

	/**
	 * Call to define the tools that should be used in this toolchain.
	 *
	 * @return {@link ToolchainData} instance describing the desired tools and their order or null if no valid data
	 *         could be selected.
	 */
	IToolchainData<T> makeToolSelection(IToolchainProgressMonitor monitor);

	/**
	 * Instead of {@link #makeToolSelection(IProgressMonitor)}, you can directly give {@link ToolchainData} to the
	 * toolchain to initialize it.
	 *
	 * @param monitor
	 * @param data
	 * @return data or null if data was an invalid selection
	 */
	IToolchainData<T> setToolSelection(IToolchainProgressMonitor monitor, IToolchainData<T> data);

	/**
	 * Initiates parsers for the previously set input files.
	 *
	 * If this method returns false, you do not have a valid parser for at least one of the selected files.
	 *
	 *
	 * @return True iff there is a usable parser for the given files and its initialization worked. False otherwise.
	 */
	boolean initializeParsers();

	/**
	 * Runs the previously select parsers
	 *
	 * @throws Exception
	 */
	void runParsers() throws Exception;

	/**
	 * If everything has been properly initiated, this method will process the set toolchain by calling
	 * {@link ToolchainWalker}.
	 *
	 * @param monitor
	 *            instance of IProgressMonitor that can be used for progress management, if in doubt, use 'null'
	 * @return A return code
	 * @throws Throwable
	 *             that is normally caused by some tool in the toolchain and results in toolchain cancellation.
	 */
	ReturnCode processToolchain(IToolchainProgressMonitor monitor) throws Throwable;

	void addAST(IElement root, ModelType outputDefinition);

	long getId();

	IToolchainData<T> getCurrentToolchainData();

	File[] getInputFiles();

	public enum ReturnCode {
		Ok, Error, Cancel
	}
}
