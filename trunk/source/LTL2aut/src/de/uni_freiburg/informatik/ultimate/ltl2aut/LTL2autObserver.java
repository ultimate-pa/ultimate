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
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
 */
public class LTL2autObserver implements IUnmanagedObserver {

	private static final String LTL_MARKER = "#LTLProperty:";

	// alphabet without X, U, F, G
	private static final String ALPHABET = "ABCDEHIJKLMNOPQRSTVWYZ";

	private final IUltimateServiceProvider mServices;
	private final IToolchainStorage mStorage;
	private final ILogger mLogger;

	private String mInputFile;
	private NWAContainer mNWAContainer;
	private LTLPropertyCheck mCheck;
	private BoogieSymbolTable mSymbolTable;

	public LTL2autObserver(final IUltimateServiceProvider services, final IToolchainStorage storage) {
		mServices = services;
		mStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		mNWAContainer = null;
		mInputFile = null;
		mSymbolTable = null;
		mCheck = null;
	}

	@Override
	public void finish() throws Throwable {
		// if there is a check, there is already boogie code
		// the ltl string is in our ACSL format, we should convert it to
		// ltl2aut format see http://www.lsv.ens-cachan.fr/~gastin/ltl2ba/
		if (mCheck == null) {
			// there is no check, so we either need to read the property from the boogie file or from the settings
			// both formats are in ltl2aut format and we need to create a check with boogie-code
			final String[] specification = getLTLProperty();
			if (specification.length > 1) {
				throw new UnsupportedOperationException(
						"We currently support only one LTL property at a time, but found " + specification.length);
			}
			mCheck = createCheckFromProperty(specification[0]);
		}
		final String ltlProperty = mCheck.getLTLProperty();
		final Map<String, CheckableExpression> irs = mCheck.getCheckableAtomicPropositions();

		final String ltl2baProperty = getLTL2BAProperty(ltlProperty);
		final AstNode node = getNeverClaim(ltl2baProperty);
		final CodeBlockFactory cbf = CodeBlockFactory.getFactory(mStorage);
		final INestedWordAutomaton<CodeBlock, String> nwa = createNWAFromNeverClaim(node, irs, mSymbolTable, cbf);
		mLogger.info("LTL Property is: " + prettyPrintProperty(irs, ltlProperty));

		mNWAContainer = new NWAContainer(nwa);
		mCheck.annotate(mNWAContainer);
	}

	private static LTLPropertyCheck createCheckFromProperty(final String ltlProperty) throws Throwable {
		final Map<String, CheckableExpression> apIrs = new LinkedHashMap<>();
		final Pattern pattern = Pattern.compile("AP\\((.*)\\)");
		final Matcher matcher = pattern.matcher(ltlProperty);
		final CheckableExpression trueLit =
				new CheckableExpression(new BooleanLiteral(null, BoogieType.TYPE_BOOL, true), Collections.emptyList());

		while (matcher.find()) {
			final String key = matcher.group(0);
			final String expr = matcher.group(1);
			apIrs.put(key, trueLit);
		}
		if (apIrs.isEmpty()) {
			throw new IllegalArgumentException("No atomic propositions in " + ltlProperty);
		}

		// we need to rename the AP(...) expressions to symbols s.t. ltl2ba does not get confused
		final Map<String, CheckableExpression> irs = new LinkedHashMap<>();
		String newLtlProperty = ltlProperty;
		int i = 0;
		for (final Entry<String, CheckableExpression> entry : apIrs.entrySet()) {
			final String freshSymbol = getAPSymbol(i);
			++i;
			newLtlProperty = newLtlProperty.replaceAll(Pattern.quote(entry.getKey()), freshSymbol);
			irs.put(freshSymbol, entry.getValue());
		}

		return new LTLPropertyCheck(newLtlProperty, irs, null);
	}

	public static String getAPSymbol(final int i) {
		if (i < ALPHABET.length()) {
			return String.valueOf(ALPHABET.charAt(i));
		}

		String rtr = "A";
		int idx = i;
		while (idx > ALPHABET.length()) {
			idx = idx - ALPHABET.length();
			rtr += String.valueOf(ALPHABET.charAt(idx % ALPHABET.length()));
		}
		return rtr;
	}

	private static String getLTL2BAProperty(final String ltlProperty) {
		String rtr = ltlProperty.toLowerCase();
		rtr = rtr.replaceAll("\\bf\\b", " <> ");
		rtr = rtr.replaceAll("\\bg\\b", " [] ");
		rtr = rtr.replaceAll("\\bx\\b", " X ");
		rtr = rtr.replaceAll("\\bu\\b", " U ");
		rtr = rtr.replaceAll("\\br\\b", " V ");
		rtr = rtr.replaceAll("<==>", "<->");
		rtr = rtr.replaceAll("==>", "->");
		rtr = rtr.replaceAll("\\s+", " ");
		return rtr;
	}

	private static String prettyPrintProperty(final Map<String, CheckableExpression> irs, final String property) {
		String rtr = property;
		for (final Entry<String, CheckableExpression> entry : irs.entrySet()) {
			rtr = rtr.replaceAll(entry.getKey(),
					"(" + BoogiePrettyPrinter.print(entry.getValue().getExpression()) + ")");
		}
		return rtr;
	}

	private String[] getLTLProperty() throws IOException {
		final String[] properties;
		if (mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.LABEL_PROPERTYFROMFILE) && mInputFile != null) {
			properties = extractPropertyFromInputFile();
			if (properties.length > 0) {
				return properties;
			}
			throw new IllegalArgumentException("File " + mInputFile + " did not contain an LTL property");
		}

		mLogger.info("Using LTL properties from settings");
		properties = mServices.getPreferenceProvider(Activator.PLUGIN_ID)
				.getString(PreferenceInitializer.LABEL_PPROPERTY).split("\n");
		if (properties.length > 0 && !properties[0].isEmpty()) {
			return properties;
		}
		throw new IllegalArgumentException("Settings did not contain an LTL property");
	}

	private String[] extractPropertyFromInputFile() throws IOException {
		BufferedReader br;
		String line = null;
		final List<String> properties = new ArrayList<>();
		try {
			br = new BufferedReader(new FileReader(mInputFile));
			while ((line = br.readLine()) != null) {
				if (line.contains(LTL_MARKER)) {
					properties.add(line.replaceFirst("//", "").replaceAll(LTL_MARKER, "").trim());
				}
			}
			br.close();
		} catch (final IOException e) {
			mLogger.error("Error while reading " + mInputFile + ": " + e);
			throw e;
		}
		return properties.toArray(new String[properties.size()]);
	}

	private AstNode getNeverClaim(final String property) throws Throwable {
		try {
			mLogger.debug("Parsing LTL property...");
			return new LTLXBAExecutor(mServices, mStorage).ltl2Ast(property);
		} catch (final Throwable e) {
			mLogger.fatal(String.format("Exception during LTL->BA execution: %s", e));
			throw e;
		}
	}

	private INestedWordAutomaton<CodeBlock, String> createNWAFromNeverClaim(final AstNode neverclaim,
			final Map<String, CheckableExpression> irs, final BoogieSymbolTable symbolTable, final CodeBlockFactory cbf)
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

		INestedWordAutomaton<CodeBlock, String> nwa;
		mLogger.debug("Transforming NeverClaim to NestedWordAutomaton...");
		try {
			// Build NWA from LTL formula in NeverClaim representation
			nwa = new Never2Automaton(neverclaim, symbolTable, irs, mLogger, mServices, cbf).getAutomaton();
			if (nwa == null) {
				throw new IllegalArgumentException("nwa is null");
			}
		} catch (final Exception e) {
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
	public boolean process(final IElement root) throws Throwable {
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
