/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * The plug-in's Observer
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.parser.util.ASTPrinter;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.cdt.CommentParser;
import de.uni_freiburg.informatik.ultimate.cdt.FunctionLineVisitor;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.ASTDecorator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.SvComp14MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.LTLPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieAstCopier;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.result.model.IResult;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 03.02.2012
 */
public class CACSL2BoogieTranslatorObserver implements IUnmanagedObserver {
	/**
	 * Whether to print the AST and some debug information for the translation, or not.
	 */
	private static final boolean mExtendedDebugOutput = false;
	/**
	 * The logger instance.
	 */
	private final Logger mLogger;
	/**
	 * A Wrapper holding the root node of the resulting Boogie AST.
	 */
	private WrapperNode mRootNode;
	private final IToolchainStorage mStorage;

	private final IUltimateServiceProvider mService;

	private final TrueWitnessExtractor mWitnessExtractor;

	public CACSL2BoogieTranslatorObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		assert storage != null;
		assert services != null;
		mStorage = storage;
		mService = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mWitnessExtractor = new TrueWitnessExtractor(mService);
	}

	@Override
	public boolean process(final IElement root) {
		if (root instanceof WitnessNode) {
			extractWitnessInformation((WitnessNode) root);
			return false;
		}

		if (!(root instanceof WrapperNode) || !((((WrapperNode) root).getBacking()) instanceof IASTTranslationUnit)) {
			// we ignore everything that will not get us an IASTTranslationUnit
			return false;
		}

		final IASTTranslationUnit inputTU = (IASTTranslationUnit) ((WrapperNode) root).getBacking();
		mWitnessExtractor.setAST(inputTU);

		if (mExtendedDebugOutput) {
			ASTPrinter.print(inputTU);
		}

		// translate to Boogie
		final Dispatcher main;
		final UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		TranslationMode mode = TranslationMode.BASE;
		try {
			mode = prefs.getEnum(CACSLPreferenceInitializer.LABEL_MODE, TranslationMode.class);
		} catch (Exception e) {
			throw new IllegalArgumentException("Unable to determine preferred mode.");
		}
		final CACSL2BoogieBacktranslator backtranslator = new CACSL2BoogieBacktranslator(mService);
		mLogger.info("Settings: " + mode);
		switch (mode) {
		case BASE:
			main = new MainDispatcher(backtranslator, mService, mLogger);
			break;
		case SV_COMP14:
			main = new SvComp14MainDispatcher(backtranslator, mService, mLogger);
			break;
		default:
			throw new IllegalArgumentException("Unknown mode.");
		}
		mStorage.putStorable(IdentifierMapping.getStorageKey(), new IdentifierMapping<String, String>());

		final ASTDecorator decorator = new ASTDecorator();
		// build a list of ACSL ASTs
		FunctionLineVisitor visitor = new FunctionLineVisitor();
		inputTU.accept(visitor);
		final CommentParser cparser = new CommentParser(inputTU.getComments(), visitor.getLineRange(), mLogger, main);
		final List<ACSLNode> acslNodes = cparser.processComments();
		validateLTLProperty(acslNodes);
		decorator.setAcslASTs(acslNodes);
		// build decorator tree
		decorator.mapASTs(inputTU);

		try {
			BoogieASTNode outputTU = main.run(decorator.getRootNode()).node;
			outputTU = (new BoogieAstCopier()).copy((Unit) outputTU);
			mRootNode = new WrapperNode(null, outputTU);
			final IdentifierMapping<String, String> map = new IdentifierMapping<String, String>();
			map.setMap(main.getIdentifierMapping());
			mStorage.putStorable(IdentifierMapping.getStorageKey(), map);
			mService.getBacktranslationService().addTranslator(backtranslator);
		} catch (final Exception t) {
			final IResult result;
			// String message =
			// "There was an error during the translation process! [" +
			// t.getClass() + ", "
			// + t.getMessage() + "]";
			if (t instanceof IncorrectSyntaxException) {
				result = new SyntaxErrorResult(Activator.PLUGIN_NAME, ((IncorrectSyntaxException) t).getLocation(),
						t.getLocalizedMessage());
			} else if (t instanceof UnsupportedSyntaxException) {
				result = new UnsupportedSyntaxResult<IElement>(Activator.PLUGIN_NAME,
						((UnsupportedSyntaxException) t).getLocation(), t.getLocalizedMessage());
			} else {
				throw t;
			}
			mService.getResultService().reportResult(Activator.PLUGIN_ID, result);
			mLogger.warn(result.getShortDescription() + " " + result.getLongDescription());
			mService.getProgressMonitorService().cancelToolchain();
		}
		return false;
	}

	private void extractWitnessInformation(final WitnessNode wnode) {
		final WitnessGraphAnnotation graphAnnot = WitnessGraphAnnotation.getAnnotation(wnode);

		switch (graphAnnot.getWitnessType()) {
		case FALSE_WITNESS:
			// is currently not handled here. May happen in the future if we want to handle assume
			break;
		case TRUE_WITNESS:
			mWitnessExtractor.setWitness(wnode);
			break;
		default:
			throw new UnsupportedOperationException("Unknown witness type " + graphAnnot.getWitnessType());
		}
	}

	private void validateLTLProperty(final List<ACSLNode> acslNodes) {
		// test "pretty printer"
		for (final ACSLNode acslNode : acslNodes) {
			if (acslNode instanceof GlobalLTLInvariant) {
				final LTLPrettyPrinter printer = new LTLPrettyPrinter();
				final String orig = printer.print(acslNode);
				mLogger.info("Original: " + orig);

				final LTLExpressionExtractor extractor = new LTLExpressionExtractor();
				final String origNormalized = printer.print(extractor.removeWeakUntil(acslNode));
				mLogger.info("Original normalized: " + origNormalized);
				if (!extractor.run(acslNode)) {
					continue;
				}
				String extracted = extractor.getLTLFormatString();
				mLogger.info("Extracted: " + extracted);
				final Set<String> equivalence = new HashSet<>();
				for (final Entry<String, Expression> subexp : extractor.getAP2SubExpressionMap().entrySet()) {
					final String exprAsString = printer.print(subexp.getValue());
					equivalence.add(exprAsString);
					mLogger.info(subexp.getKey() + ": " + exprAsString);
					extracted = extracted.replaceAll(subexp.getKey(), exprAsString);
				}
				mLogger.info("Orig from extracted: " + extracted);
				// the extraction did something weird if this does not hold
				assert extracted.equals(origNormalized);
				// our APs are not atomic if this does not hold
				assert equivalence.size() == extractor.getAP2SubExpressionMap().size();

				// TODO: Alex
				// List<VariableDeclaration> globalDeclarations = null;
				// //create this from extractor.getAP2SubExpressionMap()
				// Map<String, CheckableExpression> ap2expr = null;
				// LTLPropertyCheck x = new
				// LTLPropertyCheck(extractor.getLTLFormatString(), ap2expr,
				// globalDeclarations);
				// //annotate translation unit with x

			}
		}
		// end test
	}

	@Override
	public void finish() {
		if (mWitnessExtractor.isReady()) {

			final Map<IASTNode, String> binvariants = mWitnessExtractor.getBeforeAST2Invariants();
			final Map<IASTNode, String> ainvariants = mWitnessExtractor.getAfterAST2Invariants();

			// clear witness extractor to make him loose unused references
			//mWitnessExtractor.clear();
		}
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) {
		// Not required.
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	/**
	 * Getter for the root node.
	 * 
	 * @return the root node of the translated Boogie tree
	 */
	public IElement getRoot() {
		return mRootNode;
	}
}
