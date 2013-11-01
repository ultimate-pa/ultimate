/**
 * The plug-in's Observer
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.HashMap;

import org.apache.log4j.Logger;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.parser.util.ASTPrinter;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.cdt.CommentParser;
import de.uni_freiburg.informatik.ultimate.cdt.FunctionLineVisitor;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.ASTDecorator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.TypeErrorException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.SvComp14MainDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.WrapperNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

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
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);
	/**
	 * A Wrapper holding the root node of the resulting Boogie AST.
	 */
	private WrapperNode rootNode;

	@Override
	public boolean process(IElement root) {
		if (!(root instanceof WrapperNode)
				|| !((((WrapperNode) root).getBacking()) instanceof IASTTranslationUnit)) {
			// input not in expected format
			s_Logger.error("Unexpected input object!");
			throw new IllegalArgumentException("Not a valid input type!");
		}
		IASTTranslationUnit inputTU = (IASTTranslationUnit) ((WrapperNode) root)
				.getBacking();

		if (m_ExtendedDebugOutput) {
			ASTPrinter.print(inputTU);
		}

		ASTDecorator decorator = new ASTDecorator();
		// build a list of ACSL ASTs
		FunctionLineVisitor visitor = new FunctionLineVisitor();
		inputTU.accept(visitor);
		CommentParser cparser = new CommentParser(inputTU.getComments(),
				visitor.getLineRange());
		decorator.setAcslASTs(cparser.processComments());
		// build decorator tree
		decorator.mapASTs(inputTU);

		// translate to Boogie
		Dispatcher main;
		UltimatePreferenceStore prefs = new UltimatePreferenceStore(
				Activator.s_PLUGIN_ID);
		TranslationMode mode = TranslationMode.BASE;
		try {
			mode = prefs.getEnum(PreferenceInitializer.LABEL_MODE,
					TranslationMode.class);
		} catch (Exception e) {
			throw new IllegalArgumentException(
					"Unable to determine preferred mode.");
		}
		Backtranslator backtranslator = new Backtranslator();
		s_Logger.info("Settings: " + mode);
		switch (mode) {
		case BASE:
			main = new MainDispatcher(backtranslator);
			break;
		case SV_COMP14:
			main = new SvComp14MainDispatcher(backtranslator);
			break;
		default:
			throw new IllegalArgumentException("Unknown mode.");
		}
		UltimateServices us = UltimateServices.getInstance();
		us.setIdentifierMapping(new HashMap<String, String>());

		try {
			this.rootNode = new WrapperNode(null, main.run(decorator
					.getRootNode()).node);
			us.setIdentifierMapping(main.getIdentifierMapping());
			us.getTranslatorSequence().add(backtranslator);
		} catch (Throwable t) {
			String message = "There was an error during the translation process! ["
					+ t.getClass() + ", " + t.getMessage() + "]";

			SyntaxErrorResult<CACSLLocation> result;
			if (t instanceof UnsupportedSyntaxException
					|| t instanceof IncorrectSyntaxException
					|| t instanceof TypeErrorException) {
				// already handled - skip
			} else {
				// something unexpected happened
				// report it to the user ...
				CACSLLocation loc = new CACSLLocation(inputTU);
				result = new SyntaxErrorResult<CACSLLocation>(loc,
						Activator.s_PLUGIN_NAME, UltimateServices.getInstance()
								.getTranslatorSequence(), loc,
						SyntaxErrorType.UnsupportedSyntax);
				result.setLongDescription(message);
				us.reportResult(Activator.s_PLUGIN_ID, result);
				// Terminate the compile process with a "real" Exception,
				// visible to the Ultimate toolchain executer! Something
				// really went wrong! The core will decide what to do next!
				if (m_ExtendedDebugOutput) {
					t.printStackTrace();
				}
				throw new RuntimeException(message);
			}
			s_Logger.warn(message);
			us.cancelToolchain();
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
