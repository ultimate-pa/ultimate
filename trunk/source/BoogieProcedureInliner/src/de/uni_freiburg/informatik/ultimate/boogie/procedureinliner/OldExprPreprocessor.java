package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;
import java.util.Deque;
import java.util.ArrayDeque;

import org.omg.CORBA.Current;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Transforms a Boogie AST in to an equivalent one, where all "old" expressions (UnaryExpressions with Operator OLD),
 * inside procedures and their specifications, contain exactly one IdentifierExpression of a global variable, modifiable
 * by this procedure.
 * The process requires correct set DeclarationInformations of all IdentifierExpressions inside Procedures and their
 * specifications.
 * Meta data like Types, DeclarationInformations and so on is preserved. 
 * 
 * The set of Procedures, that still contained an "old" expressions after the conversion process,
 * can be queried afterwards.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OldExprPreprocessor extends BoogieTransformer implements IUnmanagedObserver {

	private IUltimateServiceProvider mServices;
	
	/** Maps a procedure (id) to the set of global variables (ids) it can modify, according to its specification. */
	private Map<String, Set<String>> mModifyClauses = new HashMap<>();
	
	/**
	 * All global variables, which can be modified by the procedure, according to its specification.
	 * This is the value from {@link #mModifyClauses} for the currently processed procedure.
	 */
	private Set<String> mModifiableGlobalVars;
	
	/** Contains the current stack of nested "old" expressions while processing. */
	private Deque<UnaryExpression> mOldExprStack = new ArrayDeque<>();

	/**
	 * The currently processed element is part of a "requires" specification.
	 * It is impossible that a variable was changed by the currently processed procedure before this time.
	 */
	private boolean mInRequiresSpecification = false;
	
	/** Set if an "old" expression was reinserted while processing the current declaration. */
	private boolean mReinsertedOldExpr;

	/** Identifiers of all procedures that contained at least one "old" expression after the conversion process. */
	private Set<String> mProcsContainingOldExpr = null;
	
	/** The observer changed some elements of the ast. */
	private boolean mPerformedChanges = false;
	
	public OldExprPreprocessor(IUltimateServiceProvider services) {
		mServices = services;
	}
	
	/**
	 * Returns the set of identifiers from the procedures that contained an "old" expressions inside their
	 * specifications or bodies, after they were processed by this observer.
	 * The returned set is the set from the last run. Using this observer again will create a new set.
	 * 
	 * @return The set of identifiers of all procedures that contained an "old" expression after the conversion process.
	 *         null if nothing was processed before.
	 */
	public Set<String> getProcsContainingOldExpr() {
		return mProcsContainingOldExpr;
	}
	
	@Override
	public void init() throws Throwable {
	}

	@Override
	public void finish() throws Throwable {
		System.out.println("\nContains Old: " + mProcsContainingOldExpr + "\n");
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return mPerformedChanges;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof Unit) {
			Unit astUnit = (Unit) root;
			scanModifyClauses(astUnit);
			preprocessOldExpr(astUnit);
			return false;
		}
		return false;
	}
	
	/**
	 * Initializes {@link #mModifyClauses} by scanning all modify clauses inside the ast.
	 * @param astUnit The Boogie ast.
	 */
	private void scanModifyClauses(Unit astUnit) {
		BoogieProcedureFilter filter = new BoogieProcedureFilter(mServices, astUnit);
		for (Procedure procDecl : filter.getDeclarations().values()) {
			Set<String> modifiableGlobalVars = new HashSet<>();
			for (Specification spec : procDecl.getSpecification()) {
				if (spec instanceof ModifiesSpecification) {
					for (VariableLHS globalVar : ((ModifiesSpecification) spec).getIdentifiers()) {
						modifiableGlobalVars.add(globalVar.getIdentifier());
					}
				}
			}
			mModifyClauses.put(procDecl.getIdentifier(), modifiableGlobalVars);
		}
	}
	
	private void preprocessOldExpr(Unit astUnit) {
		mProcsContainingOldExpr = new HashSet<String>();
		Declaration[] decls = astUnit.getDeclarations();
		for (int i = 0; i < decls.length; ++i) {
			if (decls[i] instanceof Procedure) {
				Procedure proc = (Procedure) decls[i];
				mReinsertedOldExpr = false;
				mModifiableGlobalVars = mModifyClauses.get(proc.getIdentifier());
				decls[i] = processDeclaration(proc);
				if (mReinsertedOldExpr) {
					mProcsContainingOldExpr.add(proc.getIdentifier());
				}
			}
		}
		// astUnit.setDeclarations not necessary, we modified the original array
		mProcsContainingOldExpr = Collections.unmodifiableSet(mProcsContainingOldExpr);
	}

	@Override
	protected Specification processSpecification(Specification spec) {
		mInRequiresSpecification = spec instanceof RequiresSpecification;
		Specification processedSpec = super.processSpecification(spec);
		mInRequiresSpecification = false;
		return processedSpec;
	}

	@Override
	protected Expression processExpression(Expression expr) {
		Expression returnValue = null;
		if (expr instanceof UnaryExpression) {
			UnaryExpression unaryExpr = (UnaryExpression) expr;
			if (unaryExpr.getOperator() == UnaryExpression.Operator.OLD) {
				mOldExprStack.push(unaryExpr);
				returnValue = processExpression(unaryExpr.getExpr());
				mOldExprStack.pop();
			}
		} else if (expr instanceof IdentifierExpression) {
			IdentifierExpression idExpr = (IdentifierExpression) expr;
			if (insideOldExpr() && isModifiableGlobalVar(idExpr) && appearsAfterModifiableContext()) {
				mReinsertedOldExpr = true;
				UnaryExpression nearestOldExpr = mOldExprStack.peek();
				returnValue = new UnaryExpression(nearestOldExpr.getLocation(),
						idExpr.getType(), UnaryExpression.Operator.OLD, idExpr);
			}
		}

		if (returnValue == null) {
			return super.processExpression(expr);
		} else {
			mPerformedChanges = true;
			return returnValue;
		}
	}
	
	/** @return Current processing takes place inside an "old" expression. */
	private boolean insideOldExpr() {
		return mOldExprStack.size() > 0;
	}

	private boolean isModifiableGlobalVar(IdentifierExpression idExpr) {
		boolean isGlobal =
				idExpr.getDeclarationInformation().getStorageClass() == DeclarationInformation.StorageClass.GLOBAL;
		boolean isModifiable = mModifiableGlobalVars.contains(idExpr.getIdentifier());
		return isModifiable && isGlobal;
	}
	
	/**
	 * @return It is possible, that variables have changed their value,
	 *         since a call of the currently processed procedure.
	 */
	private boolean appearsAfterModifiableContext() {
		return !mInRequiresSpecification;
	}

}
