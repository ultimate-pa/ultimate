/**
 * The plug-in's Observer
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

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
import de.uni_freiburg.informatik.ultimate.model.structure.WrapperNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;
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
	private static final boolean m_ExtendedDebugOutput = false;
	/**
	 * The logger instance.
	 */
	private final Logger mLogger;
	/**
	 * A Wrapper holding the root node of the resulting Boogie AST.
	 */
	private WrapperNode rootNode;
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

		if (m_ExtendedDebugOutput) {
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
		CACSL2BoogieBacktranslator backtranslator = new CACSL2BoogieBacktranslator();
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
		decorator.setAcslASTs(cparser.processComments());
		// build decorator tree
		decorator.mapASTs(inputTU);

		try {
			this.rootNode = new WrapperNode(null, main.run(decorator.getRootNode()).node);
			IdentifierMapping<String, String> map = new IdentifierMapping<String, String>();
			map.setMap(main.getIdentifierMapping());
			mStorage.putStorable(IdentifierMapping.getStorageKey(), map);
			mService.getBacktranslationService().getTranslatorSequence().add(backtranslator);
		} catch (Throwable t) {
			final IResult result;
			String message = "There was an error during the translation process! [" + t.getClass() + ", "
					+ t.getMessage() + "]";
			if (t instanceof IncorrectSyntaxException) {
				result = new SyntaxErrorResult(Activator.s_PLUGIN_NAME, ((IncorrectSyntaxException) t).getLocation(),
						t.getLocalizedMessage());
			} else if (t instanceof UnsupportedSyntaxException) {
				result = new UnsupportedSyntaxResult<IElement>(Activator.s_PLUGIN_NAME,
						((UnsupportedSyntaxException) t).getLocation(), t.getLocalizedMessage());
			} else {
				// something unexpected happened
				// report it to the user ...
				String shortDescription = t.getClass().getSimpleName();
				String longDescription = t.getLocalizedMessage();
				result = new GenericResult(Activator.s_PLUGIN_ID, shortDescription, longDescription, Severity.ERROR);
				// Terminate the compile process with a "real" Exception,
				// visible to the Ultimate toolchain executer! Something
				// really went wrong! The core will decide what to do next!
				if (m_ExtendedDebugOutput) {
					t.printStackTrace();
				}
				throw new RuntimeException(message);
			}
			mService.getResultService().reportResult(Activator.s_PLUGIN_ID, result);
			mLogger.warn(result.getShortDescription() + " " + result.getLongDescription());
			mService.getProgressMonitorService().cancelToolchain();
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.access.IObserver#finish()
	 */
	@Override
	public void finish() {
		// Not required.
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.access.IObserver#getWalkerOptions()
	 */
	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.access.IObserver#init()
	 */
	@Override
	public void init() {
		// Not required.
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.access.IObserver#performedChanges()
	 */
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
		return rootNode;
	}
}
