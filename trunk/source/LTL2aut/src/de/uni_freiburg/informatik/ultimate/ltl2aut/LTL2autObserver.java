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

import org.apache.commons.io.IOUtils;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.parser.BoogieSymbolFactory;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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
	private final ILogger mLogger;

	private String mInputFile;
	private NWAContainer mNWAContainer;
	private LTLPropertyCheck mCheck;
	private BoogieSymbolTable mSymbolTable;

	public LTL2autObserver(final IUltimateServiceProvider services) {
		mServices = services;
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
			final String[] specification = getLTLPropertyString();
			if (specification.length > 1) {
				throw new UnsupportedOperationException(
						"We currently support only one LTL property at a time, but found " + specification.length);
			}
			mCheck = createCheckFromPropertyString(specification[0]);
		}
		final Map<String, CheckableExpression> irs = mCheck.getCheckableAtomicPropositions();

		final String ltl2baProperty = mCheck.getLTL2BALTLProperty();
		final AstNode node = getNeverClaim(ltl2baProperty);
		final CodeBlockFactory cbf = CodeBlockFactory.getFactory(mServices.getStorage());
		final INestedWordAutomaton<CodeBlock, String> nwa = createNWAFromNeverClaim(node, irs, mSymbolTable, cbf);
		mLogger.info("LTL Property is: " + mCheck.getUltimateLTLProperty());

		mNWAContainer = new NWAContainer(nwa);
		mCheck.annotate(mNWAContainer);
	}

	private LTLPropertyCheck createCheckFromPropertyString(final String ltlProperty) throws Throwable {
		final Map<String, CheckableExpression> apIrs = parseAtomicPropositions(ltlProperty);
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

	// Parse atomic propositions while respecting proper parenthesis nesting.
	private Map<String, CheckableExpression> parseAtomicPropositions(final String ltlProperty) {
		final Map<String, CheckableExpression> apIrs = new LinkedHashMap<>();

		int pos = ltlProperty.indexOf("AP(");
		while (pos >= 0) {
			pos += "AP(".length();
			final int start = pos;

			int numParens = 1;
			while (numParens > 0) {
				int firstOpen = ltlProperty.indexOf("(", pos);
				int firstClose = ltlProperty.indexOf(")", pos);

				assert firstOpen >= 0 || firstClose >= 0 : "Unmatched opening parenthesis";
				if (firstOpen >= 0 && firstOpen < firstClose) {
					numParens++;
					pos = firstOpen + 1;
				} else /* if (firstClose >= 0 ) */ {
					numParens--;
					pos = firstClose + 1;
				}
			}

			final int end = pos - 1;
			final String code = ltlProperty.substring(start, end);
			final CheckableExpression expr = createCheckableExpression(code);
			apIrs.put("AP(" + code + ")", expr);

			pos = ltlProperty.indexOf("AP(", pos);
		}

		return apIrs;
	}

	private CheckableExpression createCheckableExpression(final String expr) {

		final String niceProgram = "procedure main() { #thevar := %s ;}";

		final String localProg = String.format(niceProgram, expr.trim());
		final BoogieSymbolFactory symFac = new BoogieSymbolFactory();
		final de.uni_freiburg.informatik.ultimate.boogie.parser.Lexer lexer =
				new de.uni_freiburg.informatik.ultimate.boogie.parser.Lexer(IOUtils.toInputStream(localProg));
		lexer.setSymbolFactory(symFac);
		final de.uni_freiburg.informatik.ultimate.boogie.parser.Parser p =
				new de.uni_freiburg.informatik.ultimate.boogie.parser.Parser(lexer, symFac);

		try {
			final Unit x = (Unit) p.parse().value;
			final Procedure proc = (Procedure) x.getDeclarations()[0];
			final AssignmentStatement stmt = (AssignmentStatement) proc.getBody().getBlock()[0];
			final Expression bExpr = stmt.getRhs()[0];
			final Expression newBExpr = bExpr.accept(new DeclarationInformationAdder());
			return new CheckableExpression(newBExpr, Collections.emptyList());
		} catch (final Exception e) {
			mLogger.error(String.format("Exception while parsing the atomic proposition \"%s\": %s", expr, e));
			throw new RuntimeException(e);
		}
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

	private String[] getLTLPropertyString() throws IOException {
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
			return new LTLXBAExecutor(mServices).ltl2Ast(property);
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

	private static final class DeclarationInformationAdder extends GeneratedBoogieAstTransformer {
		@Override
		public Expression transform(final IdentifierExpression node) {
			return new IdentifierExpression(node.getLocation(), node.getType(), node.getIdentifier(),
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
		}
	}

}
