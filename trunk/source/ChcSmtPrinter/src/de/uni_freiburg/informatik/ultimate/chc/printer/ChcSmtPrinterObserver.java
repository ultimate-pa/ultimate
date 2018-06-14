/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ChcSmtPrinter plug-in.
 *
 * The ULTIMATE ChcSmtPrinter plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ChcSmtPrinter plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ChcSmtPrinter plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ChcSmtPrinter plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ChcSmtPrinter plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.chc.printer;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.chc.printer.preferences.ChcSmtPrinterPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.BasePayloadContainer;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class ChcSmtPrinterObserver implements IUnmanagedObserver {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public ChcSmtPrinterObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) throws FileNotFoundException {
		final HornAnnot annot;
		{
			final BasePayloadContainer rootNode = (BasePayloadContainer) root;
			final Map<String, IAnnotations> st = rootNode.getPayload().getAnnotations();
			annot = (HornAnnot) st.get(HornUtilConstants.HORN_ANNOT_NAME);
			mLogger.debug("Printing the following HornClause set:");
			mLogger.debug(annot);
		}

		final List<HornClause> hornClauses = annot.getHornClauses();
		final HcSymbolTable symbolTable = annot.getSymbolTable();
		final ManagedScript mgdScript = annot.getScript();

		// do some categorisation of the clauses
		final List<HornClause> rules = new ArrayList<>();
		final List<HornClause> queries = new ArrayList<>();
		for (final HornClause hc : hornClauses) {
			if (hc.isHeadFalse()) {
				queries.add(hc);
			} else {
				rules.add(hc);
			}
		}


		final LoggingScript loggingScript;
		try {
			final File file = openTempFile(root);
			// TODO make an option for cse
			final boolean useCse = true;
			loggingScript = new LoggingScript(new NoopScript(), file.getAbsolutePath(), true, useCse);
		} catch (final FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			throw e;
		}

		/*
		 * Write file using loggingScript
		 */

		// set logic
		loggingScript.setLogic("HORN");

		// declare functions
		for (final HcPredicateSymbol hcPred : symbolTable.getHcPredicateSymbols()) {
			final FunctionSymbol fsym = hcPred.getFunctionSymbol();
			loggingScript.declareFun(fsym.getName(), fsym.getParameterSorts(), fsym.getReturnSort());
		}
		for (final Triple<String, Sort[], Sort> sf : symbolTable.getSkolemFunctions()) {
			loggingScript.declareFun(sf.getFirst(), sf.getSecond(), sf.getThird());
		}

		// assert constraints
		for (final HornClause hc : rules) {
			final Term formula = hc.constructFormula(mgdScript);
			loggingScript.assertTerm(formula);
		}
		// TODO: combine all queries into one
		for (final HornClause hc : queries) {
			final Term formula = hc.constructFormula(mgdScript);
			loggingScript.assertTerm(formula);
		}

		// check-sat
		loggingScript.checkSat();

		return true;
	}


	/**
	 * modified from BoogiePrinter
	 *
	 * @param root
	 * @return
	 */
	private File openTempFile(final IElement root) {
		String path;
		String filename;
		File file;

		if (mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(ChcSmtPrinterPreferenceInitializer.SAVE_IN_SOURCE_DIRECTORY_LABEL)) {
			final ILocation loc = ILocation.getAnnotation(root);
			final File inputFile = new File(loc.getFileName());
			if (inputFile.isDirectory()) {
				path = inputFile.getPath();
			} else {
				path = inputFile.getParent();
			}
			if (path == null) {
				mLogger.warn("Model does not provide a valid source location, falling back to default dump path...");
				path = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
						.getString(ChcSmtPrinterPreferenceInitializer.DUMP_PATH_LABEL);
			}
		} else {
			path = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getString(ChcSmtPrinterPreferenceInitializer.DUMP_PATH_LABEL);
		}

		try {
			if (mServices.getPreferenceProvider(Activator.PLUGIN_ID)
					.getBoolean(ChcSmtPrinterPreferenceInitializer.UNIQUE_NAME_LABEL)) {
				file = File.createTempFile(
						"ChcSmtPrinter_" + new File(ILocation.getAnnotation(root).getFileName()).getName() + "_UID",
						".bpl", new File(path));
			} else {
				filename = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
						.getString(ChcSmtPrinterPreferenceInitializer.FILE_NAME_LABEL);
				file = new File(path + File.separatorChar + filename);
				if ((!file.isFile() || !file.canWrite()) && file.exists()) {
					mLogger.warn("Cannot write to: " + file.getAbsolutePath());
					return null;
				}

				if (file.exists()) {
					mLogger.info("File already exists and will be overwritten: " + file.getAbsolutePath());
				}
				file.createNewFile();
			}
			mLogger.info("Writing to file " + file.getAbsolutePath());
			return file;

		} catch (final IOException e) {
			mLogger.fatal("Cannot open file", e);
			return null;
		}
	}

	@Override
	public void finish() {
		// not required
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// not required
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}
