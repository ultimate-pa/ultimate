package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.BoogieVarFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.CallInfoCache;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.TemporaryBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;

public class ArrayDomainToolkit<STATE extends IAbstractState<STATE>> {
	private static final String BOUND_NAME = "b";
	private static final String VALUE_NAME = "v";

	private final IAbstractDomain<STATE, IcfgEdge> mSubDomain;
	private final BoogieVarFactory mBoogieVarFactory;
	private final Boogie2SMT mBoogie2Smt;
	private final CodeBlockFactory mCodeBlockFactory;
	private final ManagedScript mManagedScript;
	private final CallInfoCache mCallInfoCache;
	private final TemporaryBoogieVar mTopValue;
	private final TemporaryBoogieVar mMinBound;
	private final TemporaryBoogieVar mMaxBound;
	private final Segmentation mDefaultSegmentation;

	public ArrayDomainToolkit(final IAbstractDomain<STATE, IcfgEdge> subDomain, final IIcfg<?> icfg,
			final IUltimateServiceProvider services, final BoogieSymbolTable boogieSymbolTable) {
		mSubDomain = subDomain;
		final BoogieIcfgContainer rootAnnotation = AbsIntUtil.getBoogieIcfgContainer(icfg);
		mBoogie2Smt = rootAnnotation.getBoogie2SMT();
		mCodeBlockFactory = rootAnnotation.getCodeBlockFactory();
		final Script script = mBoogie2Smt.getScript();
		mManagedScript = new ManagedScript(services, script);
		mBoogieVarFactory = new BoogieVarFactory(mManagedScript);
		mCallInfoCache = new CallInfoCache(icfg.getCfgSmtToolkit(), boogieSymbolTable);
		mTopValue = createValueVar(PrimitiveType.TYPE_INT);
		mMinBound = createBoundVar(PrimitiveType.TYPE_INT);
		mMaxBound = createBoundVar(PrimitiveType.TYPE_INT);
		mDefaultSegmentation = new Segmentation(Arrays.asList(mMinBound, mMaxBound), Arrays.asList(mTopValue));
	}

	public TemporaryBoogieVar createBoundVar(final IBoogieType type) {
		return mBoogieVarFactory.createFreshBoogieVar(BOUND_NAME, type);
	}

	public TemporaryBoogieVar createValueVar(final IBoogieType type) {
		return mBoogieVarFactory.createFreshBoogieVar(VALUE_NAME, type);
	}

	public IAbstractDomain<STATE, IcfgEdge> getSubDomain() {
		return mSubDomain;
	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public Script getScript() {
		return mManagedScript.getScript();
	}

	public CallInfoCache getCallInfoCache() {
		return mCallInfoCache;
	}

	public TemporaryBoogieVar getTopValue() {
		return mTopValue;
	}

	public TemporaryBoogieVar getMinBound() {
		return mMinBound;
	}

	public TemporaryBoogieVar getMaxBound() {
		return mMaxBound;
	}

	public Segmentation getDefaultSegmentation() {
		return mDefaultSegmentation;
	}

	public IAbstractStateBinaryOperator<STATE> getWideningOperator() {
		return mSubDomain.getWideningOperator();
	}

	private static <STATE extends IAbstractState<STATE>> STATE applyPostOperator(final STATE currentState,
			final IAbstractPostOperator<STATE, IcfgEdge> postOperator, final IcfgEdge transition) {
		final List<STATE> newStates = postOperator.apply(currentState, transition);
		STATE result = newStates.get(0);
		for (int i = 1; i < newStates.size(); i++) {
			result = result.union(newStates.get(i));
		}
		return result;
	}

	public STATE handleStatementBySubdomain(final STATE currentState, final Statement statement) {
		final CodeBlock codeBlock =
				mCodeBlockFactory.constructStatementSequence(null, null, statement, Origin.IMPLEMENTATION);
		return applyPostOperator(currentState, mSubDomain.getPostOperator(), codeBlock);
	}

	public Expression getExpression(final Term term) {
		return mBoogie2Smt.getTerm2Expression().translate(term);
	}

	public Term getTerm(final Expression expression) {
		// TODO: What to use here?
		final IIdentifierTranslator[] identifierTranslators = null;
		return mBoogie2Smt.getExpression2Term().translateToTerm(identifierTranslators, expression).getTerm();
	}

	public IProgramVarOrConst getBoogieVar(final IdentifierExpression expr) {
		final Boogie2SmtSymbolTable symbolTable = mBoogie2Smt.getBoogie2SmtSymbolTable();
		IProgramVarOrConst returnVar =
				symbolTable.getBoogieVar(expr.getIdentifier(), expr.getDeclarationInformation(), false);

		if (returnVar != null) {
			if (returnVar instanceof IProgramNonOldVar) {
				return ((IProgramNonOldVar) returnVar).getOldVar();
			}
			return returnVar;
		}

		returnVar = symbolTable.getBoogieConst(expr.getIdentifier());
		assert returnVar != null;
		return returnVar;
	}

	public IProgramVar getBoogieVar(final VariableLHS expr) {
		final Boogie2SmtSymbolTable symbolTable = mBoogie2Smt.getBoogie2SmtSymbolTable();
		IProgramVar rtr = symbolTable.getBoogieVar(expr.getIdentifier(), expr.getDeclarationInformation(), false);
		if (rtr == null) {
			// hack for oldvars
			final String newIdent = expr.getIdentifier().replaceAll("old\\((.*)\\)", "$1");
			rtr = symbolTable.getBoogieVar(newIdent, expr.getDeclarationInformation(), false);
			rtr = ((BoogieNonOldVar) rtr).getOldVar();
		}
		assert rtr != null : "Could not find boogie var";
		return rtr;
	}
}
