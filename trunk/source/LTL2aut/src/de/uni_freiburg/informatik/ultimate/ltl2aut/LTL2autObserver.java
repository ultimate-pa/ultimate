/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * 
 * This file is part of the ULTIMATE LTL2Aut plug-in.
 * 
 * The ULTIMATE LTL2Aut plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LTL2Aut plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LTL2Aut plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LTL2Aut plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LTL2Aut plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ltl2aut;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa.NWAContainer;
import de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa.Never2Automaton;
import de.uni_freiburg.informatik.ultimate.ltl2aut.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;

/**
 * This class reads a definition of a property in LTL and returns the AST of the description of the LTL formula as a
 * Buchi automaton.
 * 
 * @author Langenfeld
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public class LTL2autObserver implements IUnmanagedObserver {

	private static final String sLTLMarker = "#LTLProperty:";
	private static final String sIRSMarker = "#IRS:";

	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;
	private final ILogger mLogger;

	private String mInputFile;
	private NWAContainer mNWAContainer;
	private LTLPropertyCheck mCheck;
	private BoogieSymbolTable mSymbolTable;

	public LTL2autObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		mServices = services;
		mStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) {
		mNWAContainer = null;
		mInputFile = null;
		mSymbolTable = null;
		mCheck = null;
	}

	@Override
	public void finish() throws Throwable {
		// TODO: Change s.t. this plugin returns an NWA with Boogie code
		String ltlProperty;
		Map<String, CheckableExpression> irs;
		if (mCheck != null) {
			// if there is a check, there is already boogie code
			// the ltl string is in our ACSL format, we should convert it to
			// ltl2aut format
			// see http://www.lsv.ens-cachan.fr/~gastin/ltl2ba/
			ltlProperty = mCheck.getLTLProperty();
			irs = mCheck.getCheckableAtomicPropositions();
		} else {
			// there is no check, so we either need to read the property from
			// the boogie file or from the settings
			// both formats are in ltl2aut format
			// we need to create a check with boogie-code
			String[] specification = getSpecification();
			if (specification == null || specification.length == 0 || specification[0].isEmpty()) {
				throw new UnsupportedOperationException("No specification given");
			}
			ltlProperty = specification[0];
			irs = getIRS(Arrays.copyOfRange(specification, 1, specification.length));
			mCheck = new LTLPropertyCheck(ltlProperty, irs, null);
		}

		String ltl2baProperty = getLTL2BAProperty(ltlProperty);
		AstNode node = getNeverClaim(ltl2baProperty);
		CodeBlockFactory cbf = (CodeBlockFactory) mStorage
				.getStorable(CodeBlockFactory.s_CodeBlockFactoryKeyInToolchainStorage);
		NestedWordAutomaton<CodeBlock, String> nwa = createNWAFromNeverClaim(node, irs, mSymbolTable, cbf);
		mLogger.info("LTL Property is: " + prettyPrintProperty(irs, ltlProperty));

		mNWAContainer = new NWAContainer(nwa);
		mCheck.annotate(mNWAContainer);
	}

	private String getLTL2BAProperty(String ltlProperty) {
		ltlProperty = ltlProperty.toLowerCase();
		ltlProperty = ltlProperty.replaceAll("f", "<>");
		ltlProperty = ltlProperty.replaceAll("g", "[]");
		ltlProperty = ltlProperty.replaceAll("x", "X");
		ltlProperty = ltlProperty.replaceAll("u", "U");
		ltlProperty = ltlProperty.replaceAll("r", "\\/");
		ltlProperty = ltlProperty.replaceAll("<==>", "<->");
		ltlProperty = ltlProperty.replaceAll("==>", "->");
		return ltlProperty;
	}

	private String prettyPrintProperty(Map<String, CheckableExpression> irs, String property) {
		for (Entry<String, CheckableExpression> entry : irs.entrySet()) {
			property = property.replaceAll(entry.getKey(),
					"(" + BoogiePrettyPrinter.print(entry.getValue().getExpression()) + ")");
		}
		return property;
	}

	private String[] getSpecification() throws IOException {
		if (PreferenceInitializer.readPropertyFromFile()) {
			if (mInputFile != null) {
				BufferedReader br;
				String line = null;
				ArrayList<String> properties = new ArrayList<>();
				ArrayList<String> irs = new ArrayList<>();
				try {
					br = new BufferedReader(new FileReader(mInputFile));
					while ((line = br.readLine()) != null) {
						if (line.contains(sLTLMarker)) {
							properties.add(line.replaceFirst("//", "").replaceAll(sLTLMarker, "").trim());
						}
						if (line.contains(sIRSMarker)) {
							irs.add(line.replaceFirst("//", "").replaceAll(sIRSMarker, "").trim());
						}
					}
					br.close();
				} catch (IOException e) {
					mLogger.error("Error while reading " + mInputFile + ": " + e);
					line = null;
					throw e;
				}

				if (properties.isEmpty()) {
					mLogger.info("No LTL specification in input file.");
				} else {
					if (properties.size() > 1) {
						throw new UnsupportedOperationException("We currently support only 1 LTL property at a time.");
					}
					String[] rtr = new String[1 + irs.size()];
					rtr[0] = properties.get(0);
					int i = 1;
					for (String entry : irs) {
						rtr[i] = entry;
						i++;
					}
					return rtr;
				}
			}
		}

		mLogger.info("Using LTL specification from settings.");
		String property = new UltimatePreferenceStore(Activator.PLUGIN_ID)
				.getString(PreferenceInitializer.LABEL_PPROPERTY);
		return property.split("\n");
	}

	private AstNode getNeverClaim(String property) throws Throwable {
		try {
			mLogger.debug("Parsing LTL property...");
			return new LTLXBAExecutor(mServices, mStorage).ltl2Ast(property);
		} catch (Throwable e) {
			mLogger.fatal(String.format("Exception during LTL->BA execution: %s", e));
			throw e;
		}
	}

	private Map<String, CheckableExpression> getIRS(String[] entries) throws Throwable {
		// TODO: finish
		// mLogger.debug("Parsing mapping from AP to BoogieCode...");
		// Map<String, CheckableExpression> aps = new HashMap<>();
		// for (String entry : entries) {
		// try {
		//
		//
		// de.uni_freiburg.informatik.ultimate.boogie.parser.Lexer lexer = new
		// Lexer(new InputStreamReader(
		// IOUtils.toInputStream(entry.trim())));
		// de.uni_freiburg.informatik.ultimate.boogie.parser.Parser p = new
		// Parser(lexer);
		// Object x = p.parse().value;
		// // AstNode nodea = (AstNode) p.parse().value;
		// // append node to dictionary of atomic propositions
		// // if (nodea instanceof AtomicProposition) {
		// // aps.put(((AtomicProposition) nodea).getIdent(),
		// // nodea.getOutgoingNodes().get(0));
		// // }
		// } catch (Throwable e) {
		// mLogger.error(String.format("Exception while parsing the atomic proposition \"%s\": %s",
		// entry, e));
		// throw e;
		// }
		// }
		throw new UnsupportedOperationException("Unfinished");
		// return aps;
	}

	private NestedWordAutomaton<CodeBlock, String> createNWAFromNeverClaim(AstNode neverclaim,
			Map<String, CheckableExpression> irs, BoogieSymbolTable symbolTable, CodeBlockFactory cbf)
					throws Exception {
		if (neverclaim == null) {
			throw new IllegalArgumentException("There is no never claim");
		}
		if (irs == null) {
			throw new IllegalArgumentException("There are no CheckableExpressions");
		}
		if (symbolTable == null) {
			throw new IllegalArgumentException("The BoogieSymbolTable is missing");
		}
		if (cbf == null) {
			throw new IllegalArgumentException(
					"The CodeBlockFactory is missing. Did you run the RCFGBuilder before this plugin?");
		}

		NestedWordAutomaton<CodeBlock, String> nwa;
		mLogger.debug("Transforming NeverClaim to NestedWordAutomaton...");
		try {
			// Build NWA from LTL formula in NeverClaim representation
			nwa = new Never2Automaton(neverclaim, symbolTable, irs, mLogger, mServices, cbf).getAutomaton();
			if (nwa == null) {
				throw new NullPointerException("nwa is null");
			}
		} catch (Exception e) {
			mLogger.fatal("LTL2Aut encountered an error while transforming the NeverClaim to a NestedWordAutomaton");
			throw e;
		}
		return nwa;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof Unit) {
			mInputFile = ((Unit) root).getLocation().getFileName();
			mCheck = LTLPropertyCheck.getAnnotation(root);
			mSymbolTable = PreprocessorAnnotation.getAnnotation(root).getSymbolTable();
			return false;
		}
		return true;
	}

	public NWAContainer getNWAContainer() {
		return mNWAContainer;
	}

}
