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
package de.uni_freiburg.informatik.ultimate.chcprinter;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.chcprinter.preferences.ChcSmtPrinterPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornAnnot;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClauseAST;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class ChcSmtPrinterObserver extends BaseObserver {

	// TODO: make settings

	/**
	 * Add a (get-unsat-core) command after the (check-sat) command. In order to make this command work, also set the
	 * :produce-unsat-cores option and give a name to each term.
	 */
	private static final boolean PRODUCE_UNSAT_CORES = false;

	/**
	 * {@ HornClause}s can have comments attached to them. They might help understanding the meaning of each clause.
	 * This flag decides if they are printed as comments inside the smt2 file.
	 */
	private static final boolean ADD_COMMENTS = false;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	public ChcSmtPrinterObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) throws FileNotFoundException {

		if (!(root instanceof HornClauseAST)) {
			return true;
		}

		final HornAnnot annot = HornAnnot.getAnnotation(root);
		if (mLogger.isDebugEnabled()) {
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
		final File file = openTempFile(root);
		// TODO make an option for cse
		final boolean useCse = true;
		loggingScript = new LoggingScript(new NoopScript(), file.getAbsolutePath(), true, useCse);

		/*
		 * Write file using loggingScript
		 */

		// set logic
		loggingScript.setLogic("HORN");

		// add info
		{
			loggingScript.setInfo(":source",
					new QuotedObject(
							"CHC Constraint Logic: " + annot.getChcCategoryInfo().getConstraintLogic() + "\n"
							+ "                   "
							+ "Contains non-linear Horn clauses: "
									+ annot.getChcCategoryInfo().containsNonLinearHornClauses()));
		}

		if (PRODUCE_UNSAT_CORES) {
			loggingScript.setOption(":produce-unsat-cores", "true");
		}

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
			final Term formula = hc.constructFormula(mgdScript, PRODUCE_UNSAT_CORES);
			if (ADD_COMMENTS) {
				loggingScript.comment(hc.toString());
			}
			loggingScript.assertTerm(formula);
		}

		for (final HornClause hc : queries) {
			if (ADD_COMMENTS) {
				loggingScript.comment(hc.toString());
			}
			final Term formula = hc.constructFormula(mgdScript, PRODUCE_UNSAT_CORES);
			loggingScript.assertTerm(formula);
		}

		// check-sat
		loggingScript.checkSat();

		if (PRODUCE_UNSAT_CORES) {
			try {
				loggingScript.getUnsatCore();
			} catch (final UnsupportedOperationException e) {
				// do nothing
			}
		}

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
						".smt2", new File(path));
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
}
