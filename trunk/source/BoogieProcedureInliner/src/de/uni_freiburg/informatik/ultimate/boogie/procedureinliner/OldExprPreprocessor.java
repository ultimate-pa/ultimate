package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collections;
import java.util.Set;
import java.util.HashSet;
import java.util.Deque;
import java.util.ArrayDeque;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Transforms a Boogie AST in to an equivalent one, where all "old" expressions (UnaryExpressions with Operator OLD),
 * inside procedures and their specifications, contain exactly one IdentifierExpression with StorageClass GLOBAL.
 * The process requires correct set DeclarationInformations of all IdentifierExpressions inside Procedures and their
 * specifications.
 * 
 * The set of Procedures, that still contained an "old" expressions after the conversion process,
 * can be queried afterwards.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OldExprPreprocessor extends BoogieTransformer implements IUnmanagedObserver {

	/**
	 * Contains the current stack of nested "old" expressions while processing.
	 */
	private Deque<UnaryExpression> mOldExprStack = new ArrayDeque<>();
	
	/**
	 * Identifiers of all procedures that contained at least one "old" expression after the conversion process.
	 */
	private Set<String> mProcsContainingOldExpr = null;
	
	/**
	 * Set if an "old" expression was reinserted while processing the current declaration.
	 */
	private boolean mReinsertedOldExpr;
	
	@Override
	public void init() throws Throwable {
	}

	@Override
	public void finish() throws Throwable {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof Unit) {
			Unit astUnit = (Unit) root;
			processUnit(astUnit);
			return false;
		}
		return false;
	}
	
	private void processUnit(Unit astUnit) {
		mProcsContainingOldExpr = new HashSet<String>();
		Declaration[] decls = astUnit.getDeclarations();
		for (int i = 0; i < decls.length; ++i) {
			if (decls[i] instanceof Procedure) {
				Procedure proc = (Procedure) decls[i];
				mReinsertedOldExpr = false;
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
			if (insideOldExpr() && isGlobalVariable(idExpr)) {
				mReinsertedOldExpr = true;
				UnaryExpression nearestOldExpr = mOldExprStack.peek();
				returnValue = new UnaryExpression(nearestOldExpr.getLocation(), UnaryExpression.Operator.OLD, idExpr);
			}
		}
		return returnValue == null ? super.processExpression(expr) : returnValue;
	}
	
	/**
	 * @return Current processing takes place inside an "old" expression.
	 */
	private boolean insideOldExpr() {
		return mOldExprStack.size() > 0;
	}

	private boolean isGlobalVariable(IdentifierExpression idExpr) {
		assert idExpr.getDeclarationInformation() != null;
		assert idExpr.getDeclarationInformation().getStorageClass() != null;
		return idExpr.getDeclarationInformation().getStorageClass() == DeclarationInformation.StorageClass.GLOBAL;
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
}
