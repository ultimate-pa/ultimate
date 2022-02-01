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
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBException;

import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.PluginType;
import de.uni_freiburg.informatik.ultimate.core.lib.toolchain.RunDefinition;
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
	private final ICore<RunDefinition> mCore;
	private final ILogger mLogger;

	private Map<File, IToolchainData<RunDefinition>> mFoundToolchains;

	public ToolchainLocator(final File dirOrFile, final ICore<RunDefinition> core, final ILogger logger) {
		mDir = dirOrFile;
		mCore = core;
		mLogger = logger;
	}

	public Set<String> createFilterForAvailableTools() {
		final Map<File, IToolchainData<RunDefinition>> availableToolchains = locateToolchains();
		// TODO respect the options section of the tools
		// TODO: additional tools specified in the options section of this tool

		return availableToolchains.values().stream()
				.flatMap(a -> a.getRootElement().getToolchain().getPluginOrSubchain().stream())
				.filter(a -> a instanceof PluginType).map(a -> ((PluginType) a).getId().toLowerCase())
				.collect(Collectors.toSet());
	}

	public Map<File, IToolchainData<RunDefinition>> locateToolchains() {
		if (mFoundToolchains != null) {
			return Collections.unmodifiableMap(mFoundToolchains);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Trying to read toolchain files from " + mDir);
		}

		if (!mDir.exists()) {
			return Collections.emptyMap();
		}
		final File[] xmlFiles;
		if (mDir.isFile()) {
			if (mDir.getName().endsWith(".xml")) {
				xmlFiles = new File[] { mDir };
			} else {
				return Collections.emptyMap();
			}
		} else {
			xmlFiles = mDir.listFiles((file, name) -> name.endsWith(".xml"));
			if (xmlFiles.length == 0) {
				return Collections.emptyMap();
			}
		}

		mFoundToolchains = new HashMap<>();
		for (final File xmlFile : xmlFiles) {
			try {
				final IToolchainData<RunDefinition> toolchain = mCore.createToolchainData(xmlFile.getAbsolutePath());
				mFoundToolchains.put(xmlFile, toolchain);
			} catch (final FileNotFoundException e) {
				mLogger.error("Could not find file: " + e.getMessage());
			} catch (final JAXBException | SAXException e) {
				// ignore those exceptions; they just say that this file is not a valid toolchain file
			}
		}
		return Collections.unmodifiableMap(mFoundToolchains);
	}

}
