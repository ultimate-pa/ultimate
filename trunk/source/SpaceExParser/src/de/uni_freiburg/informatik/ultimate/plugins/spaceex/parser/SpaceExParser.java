/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.Unmarshaller;

import de.uni_freiburg.informatik.ultimate.core.lib.translation.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.ITranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.ObjectFactory;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.generated.Sspaceex;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExParserPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceManager;
import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceProcessor;

/**
 * @author Marius Greitschus
 *
 */
public class SpaceExParser implements ISource {

	private final String[] mFileTypes;
	private final List<String> mFileNames;
	private IUltimateServiceProvider mServices;
	private ILogger mLogger;
	private ITranslator<IcfgEdge, IcfgEdge, Term, Term, String, String> mBacktranslator;

	/**
	 * Constructor of the SpaceEx Parser plugin.
	 */
	public SpaceExParser() {
		mFileTypes = new String[] { "xml", };
		mFileNames = new ArrayList<>();
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mBacktranslator = new DefaultTranslator<>(IcfgEdge.class, IcfgEdge.class, Term.class, Term.class);
		mServices.getBacktranslationService().addTranslator(mBacktranslator);
	}

	@Override
	public void init() {
		// not necessary
	}

	@Override
	public void finish() {
		// not necessary
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return new SpaceExParserPreferenceInitializer();
	}

	@Override
	public File[] parseable(final File[] files) {
		final List<File> rtrList = Arrays.stream(files).filter(this::parseable).collect(Collectors.toList());
		return rtrList.toArray(new File[rtrList.size()]);
	}

	private boolean parseable(final File file) {

		boolean knownExtension = false;

		for (final String s : getFileTypes()) {
			if (file.getName().endsWith(s)) {
				knownExtension = true;
				break;
			}
		}

		if (!knownExtension) {
			return false;
		}

		try {
			final FileReader fr = new FileReader(file);
			final BufferedReader br = new BufferedReader(fr);
			try {
				if (!br.readLine().contains("<?xml")) {
					mLogger.debug("The input file does not contain an opening xml tag.");
					return false;
				}

				if (!br.readLine().contains("<sspaceex")) {
					mLogger.debug("The input file does not contain a spaceex tag.");
					return false;
				}
			} finally {
				br.close();
				fr.close();
			}
		} catch (final IOException ioe) {
			return false;
		}

		return true;
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		if (files.length == 1) {
			return parseAST(files[0]);
		}
		throw new UnsupportedOperationException("Cannot parse more than one file");
	}

	private IElement parseAST(final File file) throws Exception {
		// Parse the SpaceEx model
		mFileNames.add(file.getName());
		final FileInputStream fis = new FileInputStream(file);
		final JAXBContext jaxContext = JAXBContext.newInstance(ObjectFactory.class);
		final Unmarshaller unmarshaller = jaxContext.createUnmarshaller();
		final Sspaceex spaceEx = (Sspaceex) unmarshaller.unmarshal(fis);
		fis.close();
		// Initialize the preference manager + parse the config file right away.
		final SpaceExPreferenceManager preferenceManager = new SpaceExPreferenceManager(mServices, mLogger, file);
		final SpaceExPreferenceProcessor preferenceProcessor = new SpaceExPreferenceProcessor(mLogger,
				preferenceManager.getSystem(), preferenceManager.getInitially(), preferenceManager.getForbidden());
		return new SpaceExModelBuilder(spaceEx, mLogger, preferenceProcessor.getProcessedPreferences(),
				preferenceManager, mServices).getModel();
		/*
		 * final Marshaller marshaller = jaxContext.createMarshaller();
		 * marshaller.setProperty(Marshaller.JAXB_FORMATTED_OUTPUT, Boolean.TRUE); final StringWriter streamWriter = new
		 * StringWriter(); final SpaceExWriter spaceexWriter = new SpaceExWriter(mLogger); Map<String, HybridAutomaton>
		 * mergedAutomata = system.getMergedAutomata(); Sspaceex root =
		 * spaceexWriter.HybridAutomatonToSpaceEx(mergedAutomata.get( "ofOnn||controller||clock")); String targetfile =
		 * "" ; // some path/filename you want spaceexWriter.writeXmlToDisk(root,targetfile);
		 */
	}

	@Override
	public String[] getFileTypes() {
		return mFileTypes;
	}

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(Activator.PLUGIN_ID, ModelType.Type.AST, mFileNames);
		} catch (final Exception e) {
			mLogger.fatal("Oh no:", e);
		}
		return null;
	}
}
