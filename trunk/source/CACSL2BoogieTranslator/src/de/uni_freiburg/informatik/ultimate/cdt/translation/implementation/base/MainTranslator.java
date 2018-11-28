/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratedUnit;
import de.uni_freiburg.informatik.ultimate.cdt.decorator.DecoratorNode;
import de.uni_freiburg.informatik.ultimate.cdt.parser.MultiparseSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.LineDirectiveMapping;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.PreRunner.PreRunnerResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StaticObjectsHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.BitvectorTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.IntegerTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UndeclaredFunctionException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CHandlerTranslationResult;
import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode.ACSLSourceLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.CACSL2BoogieBacktranslatorMapping;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.IdentifierMapping;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness.ExtractedWitnessInvariant;

public class MainTranslator {

	private static final boolean DETERMINIZE_NECESSARY_DECLARATIONS = false;

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IToolchainStorage mStorage;
	private final WrapperNode mResult;

	public MainTranslator(final IUltimateServiceProvider services, final IToolchainStorage storage,
			final ILogger logger, final Map<IASTNode, ExtractedWitnessInvariant> witnessInvariants,
			final List<DecoratedUnit> units, final MultiparseSymbolTable symboltable, final ACSLNode acslAnnotation) {
		mServices = services;
		mLogger = logger;
		mStorage = storage;
		mResult = run(witnessInvariants, units, acslAnnotation, symboltable);
	}

	private WrapperNode run(final Map<IASTNode, ExtractedWitnessInvariant> witnessInvariants,
			final List<DecoratedUnit> units, final ACSLNode acslAnnotation, final MultiparseSymbolTable mst) {

		// if an additional Annotation was parsed put it into the root node
		if (acslAnnotation != null) {
			// (needs a fix probably) attach it to the first root node
			final DecoratorNode rootNode = units.get(0).getRootNode();
			acslAnnotation.setLocation(new ACSLSourceLocation(1, 0, 1, 0));
			rootNode.getChildren().add(0, new DecoratorNode(rootNode, acslAnnotation));
		}

		try {
			/**
			 * Multifiles: One of the main parts where dispatching has changed is the ability of dispatching a list of
			 * translation units. This is done via the list-accepting methods of both the IDispatcher and CHandler.
			 * Internally, the translation units are dispatched as single units with the difference that 'global'
			 * translation artifacts (i.e. things which only should be created once per multifile project) are only run
			 * once after all translation units have been dispatched.
			 */
			final BoogieASTNode outputTU = translate(units, witnessInvariants, mst);

			return new WrapperNode(null, outputTU);
		} catch (final IncorrectSyntaxException e) {
			final IResult result =
					new SyntaxErrorResult(Activator.PLUGIN_NAME, e.getLocation(), e.getLocalizedMessage());
			commonDoTranslationExceptionHandling(result);
			return null;
		} catch (final UnsupportedSyntaxException e) {
			final IResult result =
					new UnsupportedSyntaxResult<>(Activator.PLUGIN_NAME, e.getLocation(), e.getLocalizedMessage());
			commonDoTranslationExceptionHandling(result);
			return null;
		} catch (final UndeclaredFunctionException e) {
			final IResult result = new ExceptionOrErrorResult(Activator.PLUGIN_NAME, e);
			commonDoTranslationExceptionHandling(result);
			return null;
		}
	}

	private BoogieASTNode translate(final List<DecoratedUnit> nodes,
			final Map<IASTNode, ExtractedWitnessInvariant> witnessInvariants, final MultiparseSymbolTable mst) {

		assert !nodes.isEmpty() : "Received no nodes";

		final CTranslationResultReporter reporter = new CTranslationResultReporter(mServices, mLogger);
		final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final TranslationSettings translationSettings = new TranslationSettings(ups);
		mLogger.info(
				"Starting translation in" + (translationSettings.isSvcompMode() ? " SV-COMP mode " : " normal mode"));

		// TODO: Line Directive mapping doesn't work with multiple TUs right now
		final DecoratorNode ldmNode = nodes.stream().findFirst().get().getRootNode();
		assert ldmNode.getCNode() != null;
		assert ldmNode.getCNode() instanceof IASTTranslationUnit;

		final IASTTranslationUnit tu = (IASTTranslationUnit) ldmNode.getCNode();
		final LineDirectiveMapping lineDirectiveMapping = new LineDirectiveMapping(tu.getRawSignature());
		final LocationFactory locationFactory = new LocationFactory(lineDirectiveMapping);
		final CACSL2BoogieBacktranslatorMapping backtranslatorMapping = new CACSL2BoogieBacktranslatorMapping();

		final NameHandler nameHandler = new NameHandler(backtranslatorMapping);
		final FlatSymbolTable flatSymbolTable = new FlatSymbolTable(mLogger, mst);
		final TypeSizes typeSizes = new TypeSizes(ups, translationSettings, flatSymbolTable);

		// final ExplorativeVisitor evv = executePreRun(new ExplorativeVisitor(mLogger), nodes);

		// Build the function table
		final Map<String, IASTNode> functionTable =
				executePreRun(new FunctionTableBuilder(flatSymbolTable), nodes).getFunctionTable();

		final PreRunner preRunner = executePreRun(new PreRunner(flatSymbolTable, functionTable), nodes);
		// final NewPreRunner newPreRunner = executePreRun(new NewPreRunner(flatSymbolTable, functionTable,
		// nameHandler), nodes);
		final PreRunnerResult preRunnerResult = preRunner.getResult();

		final Set<IASTDeclaration> reachableDeclarations = initReachableDeclarations(nodes, functionTable,
				preRunnerResult.getFunctionToIndex(), translationSettings.getCheckedMethod());

		mLogger.info("Built tables and reachable declarations");
		final StaticObjectsHandler prerunStaticObjectsHandler = new StaticObjectsHandler(mLogger);
		final TypeHandler prerunTypeHandler = new TypeHandler(reporter, nameHandler, typeSizes, flatSymbolTable,
				translationSettings, locationFactory, prerunStaticObjectsHandler);

		final ExpressionTranslation prerunExpressionTranslation =
				createExpressionTranslation(translationSettings, flatSymbolTable, typeSizes, prerunTypeHandler);

		final CHandler prerunCHandler = new CHandler(mServices, mLogger, backtranslatorMapping, translationSettings,
				flatSymbolTable, functionTable, prerunExpressionTranslation, locationFactory, typeSizes,
				reachableDeclarations, prerunTypeHandler, reporter, nameHandler, prerunStaticObjectsHandler,
				preRunnerResult.getFunctionToIndex(), preRunnerResult.getVariablesOnHeap());

		final PRDispatcher prerunDispatcher = new PRDispatcher(prerunCHandler, locationFactory, prerunTypeHandler);
		prerunDispatcher.dispatch(nodes);
		mLogger.info("Completed pre-run");

		final CHandlerTranslationResult result = performMainRun(translationSettings, prerunCHandler, reporter,
				locationFactory, witnessInvariants, backtranslatorMapping, nodes, prerunTypeHandler, mst, typeSizes);
		mLogger.info("Completed translation");

		return result.getNode();
	}

	private CHandlerTranslationResult performMainRun(final TranslationSettings translationSettings,
			final CHandler prerunCHandler, final CTranslationResultReporter reporter,
			final LocationFactory locationFactory, final Map<IASTNode, ExtractedWitnessInvariant> witnessInvariants,
			final CACSL2BoogieBacktranslatorMapping backtranslatorMapping, final List<DecoratedUnit> nodes,
			final TypeHandler prerunTypeHandler, final MultiparseSymbolTable mst, final TypeSizes prerunTypeSizes) {
		final NameHandler nameHandler = new NameHandler(backtranslatorMapping);

		final FlatSymbolTable flatSymbolTable = new FlatSymbolTable(mLogger, mst);
		final ProcedureManager procedureManager = new ProcedureManager(mLogger, translationSettings);
		final StaticObjectsHandler staticObjectsHandler = new StaticObjectsHandler(mLogger);
		final TypeSizes typeSizes = new TypeSizes(prerunTypeSizes, flatSymbolTable);
		final TypeHandler typeHandler = new TypeHandler(reporter, nameHandler, typeSizes, flatSymbolTable,
				translationSettings, locationFactory, staticObjectsHandler, prerunTypeHandler);
		final ExpressionTranslation expressionTranslation =
				createExpressionTranslation(translationSettings, flatSymbolTable, typeSizes, typeHandler);

		final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer = new TypeSizeAndOffsetComputer(typeSizes,
				expressionTranslation, typeHandler, translationSettings.useBitpreciseBitfields());

		final CHandler mainCHandler = new CHandler(prerunCHandler, procedureManager, staticObjectsHandler, typeHandler,
				expressionTranslation, typeSizeAndOffsetComputer, nameHandler, flatSymbolTable, typeSizes);

		final PreprocessorHandler ppHandler =
				new PreprocessorHandler(reporter, locationFactory, translationSettings.isSvcompMode());
		final ACSLHandler acslHandler =
				new ACSLHandler(witnessInvariants != null, flatSymbolTable, expressionTranslation, typeHandler,
						procedureManager, mainCHandler.getExpressionResultTransformer(), locationFactory, mainCHandler);
		final MainDispatcher mainDispatcher = new MainDispatcher(mLogger, witnessInvariants, locationFactory,
				typeHandler, mainCHandler, ppHandler, acslHandler);

		final CHandlerTranslationResult result = mainDispatcher.dispatch(nodes);

		mStorage.putStorable(IdentifierMapping.getStorageKey(), new IdentifierMapping<>(result.getIdentifierMapping()));
		final CACSL2BoogieBacktranslator backtranslator =
				new CACSL2BoogieBacktranslator(mServices, typeSizes, backtranslatorMapping, locationFactory);
		mServices.getBacktranslationService().addTranslator(backtranslator);

		return result;
	}

	private static ExpressionTranslation createExpressionTranslation(final TranslationSettings translationSettings,
			final FlatSymbolTable flatSymbolTable, final TypeSizes typeSizes, final TypeHandler typeHandler) {
		if (translationSettings.isBitvectorTranslation()) {
			return new BitvectorTranslation(typeSizes, translationSettings, flatSymbolTable, typeHandler);
		}
		return new IntegerTranslation(typeSizes, translationSettings, typeHandler, flatSymbolTable);
	}

	private Set<IASTDeclaration> initReachableDeclarations(final List<DecoratedUnit> nodes,
			final Map<String, IASTNode> functionTable, final Map<String, Integer> functionToIndex,
			final String checkedMethod) {
		if (!DETERMINIZE_NECESSARY_DECLARATIONS) {
			return null;
		}

		// executePreRun can't be used here, as it visits all translation units after each other while the DND
		// visitor expects exactly one TU.
		final Set<IASTDeclaration> reachableDecls = new HashSet<>();
		final Map<String, Map<String, IASTDeclaration>> reverseSourceMap = new HashMap<>();
		for (final DecoratedUnit du : nodes) {
			final String key = du.getRootNode().getCNode().getContainingFilename();
			reverseSourceMap.put(key, new HashMap<>());
			for (final IASTDeclaration decl : ((IASTTranslationUnit) du.getRootNode().getCNode()).getDeclarations()) {
				if (decl instanceof IASTSimpleDeclaration) {
					final IASTSimpleDeclaration cd = (IASTSimpleDeclaration) decl;
					for (final IASTDeclarator d : cd.getDeclarators()) {
						reverseSourceMap.get(key).put(d.getName().toString(), cd);
					}
				} else if (decl instanceof IASTFunctionDefinition) {
					final IASTFunctionDefinition cd = (IASTFunctionDefinition) decl;
					reverseSourceMap.get(key).put(cd.getDeclarator().getName().toString(), cd);
				} else {
					// DND is only used for the two above so this is ok.
				}
			}
		}
		for (final DecoratedUnit du : nodes) {
			final DetermineNecessaryDeclarations dnd = new DetermineNecessaryDeclarations(checkedMethod,
					new CTranslationResultReporter(mServices, mLogger), functionTable, functionToIndex);
			du.getRootNode().getCNode().accept(dnd);
			final Set<IASTDeclaration> decl = dnd.getReachableDeclarationsOrDeclarators();
			for (final IASTDeclaration d : decl) {
				if (!d.isPartOfTranslationUnitFile()) {
					// This is not the correct declaration to store. Find the correct one!
					if (d instanceof IASTSimpleDeclaration) {
						final String name = ((IASTSimpleDeclaration) d).getDeclarators()[0].getName().toString();
						reachableDecls.add(reverseSourceMap.get(d.getContainingFilename()).get(name));
					} else if (d instanceof IASTFunctionDefinition) {
						final String name = ((IASTFunctionDefinition) d).getDeclarator().getName().toString();
						reachableDecls.add(reverseSourceMap.get(d.getContainingFilename()).get(name));
					} else {
						// Those are not regarded by DND.
					}

				} else {
					reachableDecls.add(d);
				}
			}
		}
		return reachableDecls;
	}

	private static <T extends ASTVisitor> T executePreRun(final T preRun, final Collection<DecoratedUnit> units) {
		for (final DecoratedUnit unit : units) {
			unit.getRootNode().getCNode().accept(preRun);
		}
		return preRun;
	}

	private void commonDoTranslationExceptionHandling(final IResult result) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
		mLogger.error(result.getShortDescription() + ": " + result.getLongDescription());
		mServices.getProgressMonitorService().cancelToolchain();
	}

	public WrapperNode getResult() {
		return mResult;
	}

}
