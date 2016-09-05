/*
 * Copyright (C) 2015 Björn Buchhold
 * Copyright (C) 2015 Christian Simon
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
package de.uni_freiburg.informatik.ultimate.core.lib.toolchain;

import java.io.FileNotFoundException;
import java.net.MalformedURLException;

import javax.xml.bind.JAXBException;

import org.xml.sax.SAXException;

import de.uni_freiburg.informatik.ultimate.core.model.IToolchainData;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * This implements the datastructure representing a Ultimate toolchain. It can be used for constructing a Ultimate
 * toolchain manually or from an XML specification file.
 *
 * @author Björn Buchhold
 * @author Christian Simon
 *
 */
public class ToolchainData implements IToolchainData<RunDefinition> {

	private final RunDefinition mToolchain;
	private final IToolchainStorage mStorage;
	private final IUltimateServiceProvider mServices;

	/**
	 * This constructor creates an empty toolchain.
	 *
	 * @param services
	 * @param storage
	 */
	public ToolchainData(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		this(new ToolchainFileValidator().createEmptyToolchain(), services, storage);
	}

	/**
	 * This constructor creates a toolchain from an XML file.
	 *
	 * @param xmlfile
	 *            an xml file compliant with toolchain.xsd
	 * @param services
	 * @param storage
	 * @throws JAXBException
	 * @throws FileNotFoundException
	 * @throws SAXException
	 * @throws MalformedURLException
	 */
	public ToolchainData(final String xmlfile, final IUltimateServiceProvider services, final IToolchainStorage storage)
			throws JAXBException, FileNotFoundException, SAXException {
		this(new ToolchainFileValidator().loadValidatedToolchain(xmlfile), services, storage);
	}

	private ToolchainData(final RunDefinition toolchain, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		mToolchain = toolchain;
		mServices = services;
		mStorage = storage;
	}

	/**
	 * This method adds a Plugin to the Toolchain. The plugin object must have been previously instantiated using
	 * ObjectFactory.
	 *
	 * @param plugin
	 *            object of type PluginType
	 */
	public void addPlugin(final PluginType plugin) {
		mToolchain.getToolchain().getPluginOrSubchain().add(plugin);
	}

	/**
	 * This method adds a plugin / tool to the toolchain by creating a new plugin object from a plugin name first.
	 *
	 * @param name
	 *            of the desired plugin
	 */
	@Override
	public void addPlugin(final String name) {
		final PluginType foo = new PluginType();
		foo.setId(name);
		mToolchain.getToolchain().getPluginOrSubchain().add(foo);
	}

	/**
	 * This method adds a Subchain to the Toolchain. The subchain object must have been previously instantiated using
	 * ObjectFactory.
	 *
	 * @param subchain
	 *            object of type SubchainType
	 */
	public void addSubchain(final SubchainType subchain) {
		mToolchain.getToolchain().getPluginOrSubchain().add(subchain);
	}

	/**
	 * This method appends an already existing object of type Toolchain to the end of this toolchain.
	 *
	 * @param tc
	 *            the Toolchain object to be appended to this Toolchain object
	 */
	public void addToolchain(final ToolchainData tc) {
		mToolchain.getToolchain().getPluginOrSubchain().addAll(tc.getToolchain().getToolchain().getPluginOrSubchain());
	}

	@Override
	public RunDefinition getToolchain() {
		return mToolchain;
	}

	@Override
	public IToolchainStorage getStorage() {
		return mStorage;
	}

	@Override
	public IUltimateServiceProvider getServices() {
		return mServices;
	}
}
