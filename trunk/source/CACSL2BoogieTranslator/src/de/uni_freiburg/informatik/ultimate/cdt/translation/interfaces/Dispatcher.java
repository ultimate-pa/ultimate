/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
 * Describes a dispatcher.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces;

import java.text.ParseException;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IType;

import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratorNode;
import de.uni_freiburg.informatik.ultimate.cdt.translation.LineDirectiveMapping;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.NextACSL;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IACSLHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ICHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IPreprocessorHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ISideEffectHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResultAtLocation;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.02.2012
 */
public abstract class Dispatcher {

	protected LinkedHashMap<String, Integer> mFunctionToIndex;

	protected final ILogger mLogger;

	private final IPreferenceProvider mPreferences;

	/**
	 * The side effect handler.
	 */
	public ISideEffectHandler mSideEffectHandler;
	/**
	 * The C+ACSL handler.
	 */
	public ICHandler mCHandler;
	/**
	 * The Type handler.
	 */
	public ITypeHandler mTypeHandler;
	/**
	 * The ACSL handler.
	 */
	public IACSLHandler mAcslHandler;
	/**
	 * The Name handler.
	 */
	public INameHandler mNameHandler;
	/**
	 * Holds the next ACSL node in the decorator tree.
	 */
	public NextACSL mNextAcsl;
	/**
	 * The Preprocessor statement handler.
	 */
	public IPreprocessorHandler mPreprocessorHandler;
	/**
	 * This plugin creates results for warnings if set to true.
	 */
	protected boolean mReportWarnings = true;
	/**
	 * Translation from Boogie to C for traces and expressions.
	 */
	protected final CACSL2BoogieBacktranslator mBacktranslator;
	protected final IUltimateServiceProvider mServices;

	private final TypeSizes mTypeSizes;

	private final TranslationSettings mTranslationSettings;

	private LocationFactory mLocationFactory;

	public Dispatcher(final CACSL2BoogieBacktranslator backtranslator, final IUltimateServiceProvider services,
			final ILogger logger, final LocationFactory locFac) {
		mBacktranslator = backtranslator;
		mLogger = logger;
		mServices = services;
		mPreferences = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		mTypeSizes = new TypeSizes(mPreferences);
		mTranslationSettings = new TranslationSettings(mPreferences);
		mLocationFactory = locFac;
	}

	/**
	 * Initializes the handler fields.
	 */
	protected abstract void init();

	/**
	 * Dispatch a given node to a specific handler.
	 *
	 * @param node
	 *            the node to dispatch
	 * @return the result for the given node
	 */
	public abstract Result dispatch(DecoratorNode node);

	/**
	 * Dispatch a given C node to a specific handler.
	 *
	 * @param node
	 *            the node to dispatch
	 * @return the result for the given node
	 */
	public abstract Result dispatch(IASTNode node);

	/**
	 * Dispatch a given C node to a specific handler.
	 *
	 * @param node
	 *            the node to dispatch.
	 * @return the resulting translation.
	 */
	public abstract Result dispatch(IASTPreprocessorStatement node);

	/**
	 * Dispatch a given IType to a specific handler.
	 *
	 * @param type
	 *            the type to dispatch
	 * @return the result for the given type.
	 */
	public abstract InferredType dispatch(IType type);

	/**
	 * Dispatch a given ACSL node to the specific handler.
	 *
	 * @param node
	 *            the node to dispatch
	 * @return the result for the given node
	 */
	public abstract Result dispatch(ACSLNode node);

	/**
	 * Entry point for a translation.
	 *
	 * @param node
	 *            the root node from which the translation should be started
	 * @return the result for the given node
	 */
	public final Result run(final DecoratorNode node) {
		preRun(node);
		init();
		return dispatch(node);
	}

	/**
	 * The method implementing a pre-run, if required.
	 *
	 * @param node
	 *            the node for which the pre run should be started
	 */
	protected void preRun(final DecoratorNode node) {
		assert node.getCNode() != null;
		assert node.getCNode() instanceof IASTTranslationUnit;

		final IASTTranslationUnit tu = (IASTTranslationUnit) node.getCNode();
		final LineDirectiveMapping lineDirectiveMapping = new LineDirectiveMapping(tu.getRawSignature());
		mLocationFactory = new LocationFactory(lineDirectiveMapping);
		mBacktranslator.setLocationFactory(mLocationFactory);
	}

	/**
	 * Iterates to the next ACSL statement in the decorator tree and returns a list of ACSL nodes until the next C node
	 * appears.
	 *
	 * @return a list of ACSL nodes until the next C node appears.
	 * @throws ParseException
	 *             if no trailing C node in the tree! The ACSL is in an unexpected and most probably unreachable
	 *             location and should be ignored!
	 */
	public abstract NextACSL nextACSLStatement() throws ParseException;

	/**
	 * Report a syntax error to Ultimate. This will cancel the toolchain.
	 *
	 * @param loc
	 *            where did it happen?
	 * @param type
	 *            why did it happen?
	 * @param msg
	 *            description.
	 */
	public void syntaxError(final ILocation loc, final String msg) {
		final SyntaxErrorResult result = new SyntaxErrorResult(Activator.PLUGIN_NAME, loc, msg);
		mLogger.warn(msg);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}

	/**
	 * Report a unsupported syntax to Ultimate. This will cancel the toolchain.
	 *
	 * @param loc
	 *            where did it happen?
	 * @param type
	 *            why did it happen?
	 * @param msg
	 *            description.
	 */
	public void unsupportedSyntax(final ILocation loc, final String msg) {
		final UnsupportedSyntaxResult<IElement> result = new UnsupportedSyntaxResult<>(Activator.PLUGIN_NAME, loc, msg);
		mLogger.warn(msg);
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mServices.getProgressMonitorService().cancelToolchain();
	}

	/**
	 * Report possible source of unsoundness to Ultimate.
	 *
	 * @param loc
	 *            where did it happen?
	 * @param longDesc
	 *            description.
	 */
	public void warn(final ILocation loc, final String longDescription) {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final boolean reportUnsoundnessWarning =
				prefs.getBoolean(CACSLPreferenceInitializer.LABEL_REPORT_UNSOUNDNESS_WARNING);
		if (reportUnsoundnessWarning) {
			final String shortDescription = "Unsoundness Warning";
			mLogger.warn(shortDescription + " " + longDescription);
			final GenericResultAtLocation result = new GenericResultAtLocation(Activator.PLUGIN_NAME, loc,
					shortDescription, longDescription, Severity.WARNING);
			mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		}
	}

	/**
	 * Getter for the setting: checked method.
	 *
	 * @return the checked method's name.
	 */
	public String getCheckedMethod() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		String checkMethod = SFO.EMPTY;
		try {
			checkMethod = prefs.getString(CACSLPreferenceInitializer.MAINPROC_LABEL);
		} catch (final Exception e) {
			throw new IllegalArgumentException("Unable to determine specified checked method.");
		}
		return checkMethod;
	}

	/**
	 * Whether the memory model is required or not.
	 *
	 * @return whether the memory model is required or not.
	 * @deprecated use check of MemoryHanlder instead
	 */
	@Deprecated
	public abstract boolean isMMRequired();

	/**
	 * Getter for the identifier mapping.
	 *
	 * @return the mapping of Boogie identifiers to origin C identifiers.
	 */
	public Map<String, String> getIdentifierMapping() {
		return mCHandler.getSymbolTable().getIdentifierMapping();
	}

	public LinkedHashMap<String, Integer> getFunctionToIndex() {
		return mFunctionToIndex;
	}

	public TypeSizes getTypeSizes() {
		return mTypeSizes;
	}

	public TranslationSettings getTranslationSettings() {
		return mTranslationSettings;
	}

	public abstract LinkedHashSet<IASTDeclaration> getReachableDeclarationsOrDeclarators();

	public IPreferenceProvider getPreferences() {
		return mPreferences;
	}

	public LocationFactory getLocationFactory() {
		return mLocationFactory;
	}

	public static final class TranslationSettings {
		private final PointerCheckMode mDivisionByZeroOfIntegerTypes;
		private final PointerCheckMode mDivisionByZeroOfFloatingTypes;

		public TranslationSettings(final IPreferenceProvider preferences) {
			mDivisionByZeroOfIntegerTypes = preferences.getEnum(
					CACSLPreferenceInitializer.LABEL_CHECK_DIVISION_BY_ZERO_OF_INTEGER_TYPES, PointerCheckMode.class);
			mDivisionByZeroOfFloatingTypes = preferences.getEnum(
					CACSLPreferenceInitializer.LABEL_CHECK_DIVISION_BY_ZERO_OF_FLOATING_TYPES, PointerCheckMode.class);

		}

		public PointerCheckMode getDivisionByZeroOfIntegerTypes() {
			return mDivisionByZeroOfIntegerTypes;
		}

		public PointerCheckMode getDivisionByZeroOfFloatingTypes() {
			return mDivisionByZeroOfFloatingTypes;
		}
	}
}
