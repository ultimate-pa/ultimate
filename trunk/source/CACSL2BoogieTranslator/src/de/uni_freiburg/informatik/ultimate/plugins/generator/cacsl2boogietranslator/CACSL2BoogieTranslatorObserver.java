/**
 * The plug-in's Observer
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
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
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.LTLPrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GlobalLTLInvariant;
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 03.02.2012
 */
public class CACSL2BoogieTranslatorObserver implements IUnmanagedObserver {
	/**
	 * Whether to print the AST and some debug information for the translation,
	 * or not.
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
	private IToolchainStorage mStorage;

	private IUltimateServiceProvider mService;

	public CACSL2BoogieTranslatorObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		assert storage != null;
		assert services != null;
		mStorage = storage;
		mService = services;
		mLogger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
	}

	@Override
	public boolean process(IElement root) {
		if (!(root instanceof WrapperNode) || !((((WrapperNode) root).getBacking()) instanceof IASTTranslationUnit)) {
			// input not in expected format
			mLogger.error("Unexpected input object!");
			throw new IllegalArgumentException("Not a valid input type!");
		}
		IASTTranslationUnit inputTU = (IASTTranslationUnit) ((WrapperNode) root).getBacking();

		if (mExtendedDebugOutput) {
			ASTPrinter.print(inputTU);
		}

		// translate to Boogie
		Dispatcher main;
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		TranslationMode mode = TranslationMode.BASE;
		try {
			mode = prefs.getEnum(CACSLPreferenceInitializer.LABEL_MODE, TranslationMode.class);
		} catch (Exception e) {
			throw new IllegalArgumentException("Unable to determine preferred mode.");
		}
		CACSL2BoogieBacktranslator backtranslator = new CACSL2BoogieBacktranslator(mService);
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

		ASTDecorator decorator = new ASTDecorator();
		// build a list of ACSL ASTs
		FunctionLineVisitor visitor = new FunctionLineVisitor();
		inputTU.accept(visitor);
		CommentParser cparser = new CommentParser(inputTU.getComments(), visitor.getLineRange(), mLogger, main);
		List<ACSLNode> acslNodes = cparser.processComments();
		// test "pretty printer"
		for (ACSLNode acslNode : acslNodes) {
			if (acslNode instanceof GlobalLTLInvariant) {
				LTLPrettyPrinter printer = new LTLPrettyPrinter();
				mLogger.info(printer.print(acslNode));
				LTLExpressionExtractor extractor = new LTLExpressionExtractor();
				if (!extractor.run(acslNode)) {
					continue;
				}
				mLogger.info(extractor.getLTLFormatString());
				for (Entry<String, Expression> subexp : extractor.getAP2SubExpressionMap().entrySet()) {
					mLogger.info(subexp.getKey() + ": " + printer.print(subexp.getValue()));
				}

				//TODO: Alex
//				List<VariableDeclaration> globalDeclarations = null;
//				//create this from extractor.getAP2SubExpressionMap()
//				Map<String, CheckableExpression> ap2expr = null;
//				LTLPropertyCheck x = new LTLPropertyCheck(extractor.getLTLFormatString(), ap2expr, globalDeclarations);
//				//annotate translation unit with x 

			}
		}
		// end test
		decorator.setAcslASTs(acslNodes);
		// build decorator tree
		decorator.mapASTs(inputTU);

		try {
			mRootNode = new WrapperNode(null, main.run(decorator.getRootNode()).node);
			IdentifierMapping<String, String> map = new IdentifierMapping<String, String>();
			map.setMap(main.getIdentifierMapping());
			mStorage.putStorable(IdentifierMapping.getStorageKey(), map);
			mService.getBacktranslationService().addTranslator(backtranslator);
		} catch (Exception t) {
			final IResult result;
			// String message =
			// "There was an error during the translation process! [" +
			// t.getClass() + ", "
			// + t.getMessage() + "]";
			if (t instanceof IncorrectSyntaxException) {
				result = new SyntaxErrorResult(Activator.s_PLUGIN_NAME, ((IncorrectSyntaxException) t).getLocation(),
						t.getLocalizedMessage());
			} else if (t instanceof UnsupportedSyntaxException) {
				result = new UnsupportedSyntaxResult<IElement>(Activator.s_PLUGIN_NAME,
						((UnsupportedSyntaxException) t).getLocation(), t.getLocalizedMessage());
			} else {
				throw t;
			}
			mService.getResultService().reportResult(Activator.s_PLUGIN_ID, result);
			mLogger.warn(result.getShortDescription() + " " + result.getLongDescription());
			mService.getProgressMonitorService().cancelToolchain();
		}
		return false;
	}

	@Override
	public void finish() {
		// Not required.
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public void init() {
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
