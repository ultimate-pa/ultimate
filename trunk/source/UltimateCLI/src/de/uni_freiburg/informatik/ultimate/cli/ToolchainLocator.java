/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE CLI plug-in.
 *
 * The ULTIMATE CLI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CLI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CLI plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CLI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CLI plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cli;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.JAXBException;

import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.ToolchainListType;
import de.uni_freiburg.informatik.ultimate.core.model.ICore;
import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 *
 * This class searches for feasible toolchain files in the current working directory and loads them s.t. we can filter
 * settings based on their contents.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ToolchainLocator {

	private final File mDir;
	private final ICore<ToolchainListType> mCore;
	private final ILogger mLogger;

	public ToolchainLocator(final File directory, final ICore<ToolchainListType> core, final ILogger logger) {
		mDir = directory;
		mCore = core;
		mLogger = logger;
	}

	public void loadToolchains() {
		mLogger.debug("Trying to read toolchain files from " + mDir);

		if (!mDir.exists()) {
			return;
		}

		if (!mDir.isDirectory()) {
			return;
		}

		final File[] xmlFiles = mDir.listFiles((file, name) -> name.endsWith(".xml"));
		if (xmlFiles.length == 0) {
			return;
		}

		final List<IToolchainData<ToolchainListType>> toolchains = new ArrayList<>();
		for (final File xmlFile : xmlFiles) {
			try {
				final IToolchainData<ToolchainListType> toolchain =
						mCore.createToolchainData(xmlFile.getAbsolutePath());
				toolchains.add(toolchain);
			} catch (final FileNotFoundException e) {
				mLogger.error("Could not find file: " + e.getMessage());
			} catch (final JAXBException e) {
			} catch (final SAXException e) {
			}
		}

		toolchains.stream().forEach(a -> mLogger.debug(a.toString()));

	}
}
