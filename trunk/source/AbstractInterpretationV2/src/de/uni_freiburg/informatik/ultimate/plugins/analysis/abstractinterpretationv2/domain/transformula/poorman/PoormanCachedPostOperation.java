package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman;

import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.MappedTerm2Expression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.util.AssumptionBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.util.TermConjunctEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;

public class PoormanCachedPostOperation<BACKING extends IAbstractState<BACKING>> {

	private final Set<IProgramVarOrConst> mAddedVariables;
	private final Map<TermVariable, String> mAlternateOldNames;
	private final IAbstractDomain<BACKING, IcfgEdge> mBackingDomain;
	private final Boogie2SMT mBoogie2Smt;
	private final Boogie2SmtSymbolTableTmpVars mBoogie2SmtSymbolTable;
	private final Map<String, IProgramVar> mFreshVarsCache;
	private final CodeBlock mHavocPostCodeBlock;
	private final Set<IProgramVarOrConst> mInAuxVars;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final MappedTerm2Expression mMappedTerm2Expression;
	private final Set<IProgramVarOrConst> mNewAuxVars;
	private final Set<IProgramVarOrConst> mNewOutVars;
	private final Map<TermVariable, IProgramVarOrConst> mOldTermVarMapping;
	private final Map<IProgramVarOrConst, IProgramVarOrConst> mOutVarRenaming;
	private final Map<IProgramVarOrConst, IProgramVarOrConst> mRenamedInVars;
	private final IUltimateServiceProvider mServices;
	private final UnmodifiableTransFormula mTransformula;

	private final Set<TermVariable> mVariableRetainmentSet;
	private final TermConjunctEvaluator<BACKING> mEvaluator;

	protected PoormanCachedPostOperation(final UnmodifiableTransFormula transformula,
			final IUltimateServiceProvider services, final Boogie2SMT boogie2Smt, final ManagedScript managedScript,
			final IBoogieSymbolTableVariableProvider variableProvider, final CodeBlockFactory codeBlockFactory,
			final IAbstractDomain<BACKING, IcfgEdge> backingDomain) {
		mFreshVarsCache = new HashMap<>();
		mTransformula = transformula;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mBackingDomain = backingDomain;
		mBoogie2Smt = boogie2Smt;
		assert variableProvider instanceof Boogie2SmtSymbolTableTmpVars;
		mBoogie2SmtSymbolTable = (Boogie2SmtSymbolTableTmpVars) variableProvider;
		mManagedScript = managedScript;
		mMappedTerm2Expression = new MappedTerm2Expression(mBoogie2Smt.getTypeSortTranslator(),
				mBoogie2Smt.getBoogie2SmtSymbolTable(), mManagedScript);

		mRenamedInVars = new HashMap<>();
		mNewOutVars = new HashSet<>();
		mNewAuxVars = new HashSet<>();
		mOutVarRenaming = new HashMap<>();
		mAddedVariables = new HashSet<>();
		mInAuxVars = new HashSet<>();

		mVariableRetainmentSet = new HashSet<>();
		mOldTermVarMapping = new HashMap<>();
		mAlternateOldNames = new HashMap<>();
		// Out-, in- and aux-vars have a different name in the transformula than in the state. These names will be
		// translated into an assume expression in which the same names occur. These "new" variables do not have a
		// representation in the symbol table, therefore, they are added to the variableRetainmentSet which indicates
		// the translator to ignore the symbol table and just create a new variable expression.
		for (final Entry<IProgramVar, TermVariable> varEntry : mTransformula.getOutVars().entrySet()) {
			if (varEntry.getKey() instanceof BoogieOldVar) {
				// Construct a new variable name from old(x): old~~x
				final String termVarName =
						"old~~".concat(varEntry.getValue().getName().replace("old(", "").replace(")", ""));
				mAlternateOldNames.put(varEntry.getValue(), termVarName);
				final IProgramVarOrConst newProgramVarFromOld =
						getCachedFreshProgramVar(varEntry.getValue(), termVarName);
				mOldTermVarMapping.put(varEntry.getValue(), newProgramVarFromOld);
			} else {
				mVariableRetainmentSet.add(varEntry.getValue());
			}
		}
		mVariableRetainmentSet.addAll(mTransformula.getInVars().values());
		mVariableRetainmentSet.addAll(mTransformula.getAuxVars());

		obtainVariableMappingFromTransformula();
		final HavocStatement havocStmt = constructBoogieHavocStatementOfUnmappedOutVars();
		if (havocStmt == null) {
			mHavocPostCodeBlock = null;
		} else {
			mHavocPostCodeBlock = AssumptionBuilder.constructCodeBlock(codeBlockFactory, havocStmt);
		}

		mEvaluator =
				new TermConjunctEvaluator<>(mLogger, transformula.getFormula(), mBackingDomain, mVariableRetainmentSet,
						mAlternateOldNames, mMappedTerm2Expression, codeBlockFactory, mBoogie2Smt.getScript());
	}

	/**
	 * Variables that occur in the inVars but not in the outVars are implicitly havoc'ed. Also, if a program variable
	 * occurs in the outVars and is mapped to a {@link TermVariable} that is not occurring in the {@link Term}, the
	 * variable is havoc'ed implicitly. This method constructs such a {@link HavocStatement}.
	 *
	 * @return A havoc statement in which the implicitly havoc'ed variables are explicitly havoc'ed. If none exists,
	 *         <code>null</code> is returned.
	 */
	private HavocStatement constructBoogieHavocStatementOfUnmappedOutVars() {
		// Variable occurs in inVars, but not in outVars
		final Set<TermVariable> hvcVar = mTransformula.getInVars().entrySet().stream()
				.filter(entry -> !mTransformula.getOutVars().keySet().contains(entry.getKey()))
				.map(entry -> entry.getValue()).collect(Collectors.toSet());

		assert hvcVar != null;

		final Set<TermVariable> tvSet = new HashSet<>(Arrays.asList(mTransformula.getFormula().getFreeVars()));

		// Variables in out vars that are not free are havoced as well.
		hvcVar.addAll(mTransformula.getOutVars().entrySet().stream().filter(entry -> !tvSet.contains(entry.getValue()))
				.map(Entry<IProgramVar, TermVariable>::getValue).collect(Collectors.toSet()));

		if (hvcVar.isEmpty()) {
			return null;
		}

		final List<VariableLHS> variableLHSs = new ArrayList<>();

		for (final TermVariable tVar : hvcVar) {
			variableLHSs.add(new VariableLHS(null, mBoogie2Smt.getTypeSortTranslator().getType(tVar.getSort()),
					tVar.getName(), new DeclarationInformation(StorageClass.IMPLEMENTATION, null)));
		}

		final HavocStatement havoc =
				new HavocStatement(null, variableLHSs.toArray(new VariableLHS[variableLHSs.size()]));

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("The following variables are havoced by this transformula: " + variableLHSs);
		}

		return havoc;
	}

	protected Map<TermVariable, String> getAlternateOldNames() {
		return mAlternateOldNames;
	}

	private IProgramVar getCachedFreshProgramVar(final TermVariable var) {
		return getCachedFreshProgramVar(var, var.getName());
	}

	private IProgramVar getCachedFreshProgramVar(final TermVariable var, final String alternateName) {
		if (mFreshVarsCache.containsKey(alternateName)) {
			return mFreshVarsCache.get(alternateName);
		}
		final IProgramVar freshProgramVar = new MockupProgramVar(var, alternateName, mManagedScript);
		mFreshVarsCache.put(alternateName, freshProgramVar);
		return freshProgramVar;
	}

	protected Set<TermVariable> getVariableRetainmentSet() {
		return mVariableRetainmentSet;
	}

	/**
	 * Fills for a given transformula the given maps and sets with sensible values, depending on the variables in the
	 * transformula. See its usage in, e.g., the {@link #widen(PoormanAbstractState, IcfgEdge)} function.
	 *
	 * @param outVarRenaming
	 *            Is filled with the mapping of program variables to outVars of the transformula to be able to rename
	 *            the variables in the abstract state back to their original ones after applying the abstract post.
	 * @param addedVariables
	 *            Is filled with all variables that need to be added to the abstract state in order to be able to apply
	 *            the abstract post for the given transformula correctly.
	 * @param inAuxVars
	 *            Is filled with all variables that need to be removed from the computed post state after applying the
	 *            post operator to restore the original variables.
	 */
	private void obtainVariableMappingFromTransformula() {
		assert mRenamedInVars.isEmpty();
		assert mNewOutVars.isEmpty();
		assert mNewAuxVars.isEmpty();
		assert mOutVarRenaming.isEmpty();
		assert mAddedVariables.isEmpty();
		assert mInAuxVars.isEmpty();

		// Collect inVars that are to be renamed.
		// If in a state there is variable x and the transformula's inVars state that {x -> x_1}, then rename x to x_1
		// in the current state. If the variable is a renamed old variable, take this into account.
		mRenamedInVars.putAll(mTransformula.getInVars().entrySet().stream()
				.collect(Collectors.toMap(Entry<IProgramVar, TermVariable>::getKey, entry -> {
					if (mOldTermVarMapping.containsKey(entry.getValue())) {
						return mOldTermVarMapping.get(entry.getValue());
					}
					return getCachedFreshProgramVar(entry.getValue());
				})));

		// Collect the names of all outVars in the transformula and add fresh variables that are to be added as fresh
		// variables to the state.
		// For example, if the outVars state that {x -> x_2}, construct a fresh variable x_2 which is added later to the
		// state.
		// In the case where the outVar is also an inVar, e.g. inVars = {x -> x_1} and outVars = {x -> x_1}, x_1 has
		// already been added to the state in the inVars and will not be added again, here.
		for (final Entry<IProgramVar, TermVariable> entry : mTransformula.getOutVars().entrySet()) {
			if (!mRenamedInVars.values().stream()
					.anyMatch(var -> var.getGloballyUniqueId().equals(entry.getValue().getName()))) {
				final IProgramVarOrConst newOutVar;
				if (mOldTermVarMapping.containsKey(entry.getValue())) {
					newOutVar = mOldTermVarMapping.get(entry.getValue());
				} else {
					newOutVar = getCachedFreshProgramVar(entry.getValue());
					mNewOutVars.add(newOutVar);
				}
				mOutVarRenaming.put(newOutVar, entry.getKey());
			} else {
				// In this case, the outVar is also an inVar. Thus, the corresponding inVar needs to be added to the
				// renaming map to be able to restore the state after the application of abstract post.
				final Entry<IProgramVarOrConst, IProgramVarOrConst> correspondingInVar = mRenamedInVars.entrySet()
						.stream().filter(e -> e.getValue().getGloballyUniqueId().equals(entry.getValue().getName()))
						.findFirst().orElseGet(() -> {
							throw new UnsupportedOperationException();
						});
				mOutVarRenaming.put(correspondingInVar.getValue(), correspondingInVar.getKey());
			}
		}

		// Collect the auxVars of the transformula that are to be added to the abstract state.
		for (final TermVariable auxVar : mTransformula.getAuxVars()) {
			if (!mRenamedInVars.values().stream().anyMatch(var -> var.getGloballyUniqueId().equals(auxVar.getName()))
					&& !mNewOutVars.stream().anyMatch(var -> var.getGloballyUniqueId().equals(auxVar.getName()))) {
				final IProgramVarOrConst newAuxVar = getCachedFreshProgramVar(auxVar);
				mNewAuxVars.add(newAuxVar);
			}
		}

		mAddedVariables.addAll(Stream.concat(mNewOutVars.stream(), mNewAuxVars.stream()).collect(Collectors.toSet()));

		// Collect in and aux vars that are removed later from the abstract state
		mInAuxVars
				.addAll(mRenamedInVars.values().stream()
						.filter(var -> !mTransformula.getOutVars().values().stream()
								.anyMatch(out -> out.getName().equals(var.getGloballyUniqueId())))
						.collect(Collectors.toSet()));

		for (final TermVariable outVar : mTransformula.getOutVars().values()) {
			if (mOldTermVarMapping.containsKey(outVar)) {
				mInAuxVars.remove(mOldTermVarMapping.get(outVar));
			}
		}
		mInAuxVars.addAll(mNewAuxVars);

		// Some logging output to debug renaming
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("   Will rename the following variables in the pre state:");
			mRenamedInVars.entrySet().stream()
					.forEach(entry -> mLogger.debug("     " + entry.getKey().getGloballyUniqueId() + " ("
							+ entry.getKey().hashCode() + ") --> " + entry.getValue().getGloballyUniqueId() + " ("
							+ entry.getValue().hashCode() + ")"));
			mLogger.debug("   Will add the following variables to the pre state: " + mAddedVariables);
			mLogger.debug("   Will remove the following variables from the post state(s): " + mInAuxVars);
			mLogger.debug("   Will rename the following variables in the post state(s):");
			mOutVarRenaming.entrySet().stream()
					.forEach(entry -> mLogger.debug("     " + entry.getKey().getGloballyUniqueId() + " ("
							+ entry.getKey().hashCode() + ") --> " + entry.getValue().getGloballyUniqueId() + " ("
							+ entry.getValue().hashCode() + ")"));
		}
	}

	protected PoormanAbstractState<BACKING> prepareState(final PoormanAbstractState<BACKING> input) {

		// Add temporary variables to the symbol table
		final Set<IProgramVarOrConst> tempVars = new HashSet<>();
		tempVars.addAll(mRenamedInVars.values());
		tempVars.addAll(mNewOutVars);
		tempVars.addAll(mNewAuxVars);
		mBoogie2SmtSymbolTable
				.addTemporaryVariables(tempVars.stream().map(var -> (IProgramVar) var).collect(Collectors.toSet()));

		return input.renameVariables(mRenamedInVars).addVariables(mAddedVariables);
	}

	protected Collection<BACKING> applyPost(final PoormanAbstractState<BACKING> preState) {
		return mEvaluator.computePost(preState);
	}

	protected Collection<PoormanAbstractState<BACKING>>
			restoreOriginalStateVariables(final Collection<BACKING> states) {
		Collection<BACKING> postPostStates = new HashSet<>();
		if (mHavocPostCodeBlock != null) {
			for (final BACKING postState : states) {
				if (postState.isBottom()) {
					continue;
				}

				// TODO: Move application of havoc to application of POST!
				final Collection<BACKING> havocedPostStates =
						mBackingDomain.getPostOperator().apply(postState, mHavocPostCodeBlock);

				mLogger.debug("Post-havoc states: " + havocedPostStates);
				if (havocedPostStates.size() != 1) {
					throw new UnsupportedOperationException(
							"The number of states after the application of a havoc statement should be one, but is something else here.");
				}
				postPostStates.addAll(havocedPostStates);
			}
		}

		if (mHavocPostCodeBlock == null || postPostStates.isEmpty()) {
			postPostStates = states;
		}

		// Remove all added temporary variables from the symbol table
		mBoogie2SmtSymbolTable.clearTemporaryVariables();

		final List<PoormanAbstractState<BACKING>> returnList = new ArrayList<>();
		for (final BACKING state : postPostStates) {
			// Remove all variables that are the target of the renaming later on
			final Set<IProgramVarOrConst> removeOverwrittenOuts = state.getVariables().stream()
					.filter(var -> mOutVarRenaming.values().stream()
							.anyMatch(out -> var.getGloballyUniqueId().equals(out.getGloballyUniqueId())))
					.collect(Collectors.toSet());

			final BACKING newBackingState = state.removeVariables(removeOverwrittenOuts).removeVariables(mInAuxVars)
					.renameVariables(mOutVarRenaming);

			returnList.add(new PoormanAbstractState<>(mServices, mBackingDomain, newBackingState));
		}

		return returnList;
	}

	/**
	 * Mockup Program var for internal purposes only.
	 *
	 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class MockupProgramVar implements IProgramVar {
		private static final long serialVersionUID = 4924620166368141045L;

		private final String mName;
		private final TermVariable mTerm;
		private final TermVariable mVar;

		private MockupProgramVar(final TermVariable var, final String alternateName,
				final ManagedScript managedScript) {
			mVar = var;
			mName = alternateName;
			mTerm = managedScript.variable(mName, mVar.getSort());
		}

		@Override
		public ApplicationTerm getDefaultConstant() {
			return null;
		}

		@Override
		public String getGloballyUniqueId() {
			return mName;
		}

		@Override
		public ApplicationTerm getPrimedConstant() {
			return null;
		}

		@Override
		public String getProcedure() {
			return null;
		}

		@Override
		public Term getTerm() {
			return getTermVariable();
		}

		@Override
		public TermVariable getTermVariable() {
			return mTerm;
		}

		@Override
		public boolean isGlobal() {
			return false;
		}

		@Override
		public boolean isOldvar() {
			return false;
		}

		private void readObject(final java.io.ObjectInputStream in) throws IOException, ClassNotFoundException {
			throw new IOException("Unserializable object: " + getClass().getSimpleName());
		}

		@Override
		public String toString() {
			return getGloballyUniqueId();
		}

		private void writeObject(final ObjectOutputStream out) throws IOException {
			throw new IOException("Unserializable object: " + getClass().getSimpleName());
		}
	}
}
