/**
 * 
 */
package soottocfg.soot.transformers;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import soot.Body;
import soot.BooleanType;
import soot.Hierarchy;
import soot.Immediate;
import soot.IntType;
import soot.Local;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.jimple.AnyNewExpr;
import soot.jimple.ArrayRef;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.IdentityRef;
import soot.jimple.IfStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InstanceOfExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.NullConstant;
import soot.jimple.Ref;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.SwitchStmt;
import soot.jimple.ThrowStmt;
import soot.jimple.UnopExpr;
import soot.jimple.toolkits.annotation.nullcheck.NullnessAnalysis;
import soot.tagkit.Host;
import soottocfg.util.Pair;

/**
 * @author schaef
 *
 */
public class ExceptionTransformer extends AbstractTransformer {

	private NullnessAnalysis nullnessAnalysis;
	protected final SootClass exceptionClass, nulLPointerExceptionClass, arrayIndexOutOfBoundsExceptionClass,
			classCastExceptionClass;

	protected Local exceptionVariable;
	private final SootMethod internalAssertMethod;

	private static final String exceptionLocalName = "$exception";

	public static final String getExceptionLocalName() {
		return ExceptionTransformer.exceptionLocalName;
	}

	/**
	 * 
	 */
	public ExceptionTransformer(NullnessAnalysis nna) {
		nullnessAnalysis = nna;
		exceptionClass = Scene.v().getSootClass("java.lang.Exception");
		nulLPointerExceptionClass = Scene.v().getSootClass("java.lang.NullPointerException");
		arrayIndexOutOfBoundsExceptionClass = Scene.v().getSootClass("java.lang.ArrayIndexOutOfBoundsException");
		classCastExceptionClass = Scene.v().getSootClass("java.lang.ClassCastException");

		internalAssertMethod = AssertionReconstruction.v().getAssertMethod();

	}

	public Local getExceptionVariable() {
		return this.exceptionVariable;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see soot.BodyTransformer#internalTransform(soot.Body, java.lang.String,
	 * java.util.Map)
	 */
	@Override
	protected void internalTransform(Body body, String arg1, Map<String, String> arg2) {
		Map<Unit, List<ConditionalExceptionContainer>> needsHandling = new HashMap<Unit, List<ConditionalExceptionContainer>>();

		exceptionVariable = Jimple.v().newLocal(ExceptionTransformer.exceptionLocalName, RefType.v(exceptionClass));
		body.getLocals().add(exceptionVariable);

		Hierarchy h = Scene.v().getActiveHierarchy();

		PatchingChain<Unit> units = body.getUnits();
		for (Unit u : units) {
			List<ConditionalExceptionContainer> result = collectPossibleExceptions(u);
			if (!result.isEmpty()) {
				needsHandling.put(u, result);
			}
		}

		for (Entry<Unit, List<ConditionalExceptionContainer>> entry : needsHandling.entrySet()) {
			Unit u = entry.getKey();
			List<Trap> possibleTraps = getTrapsGuardingUnit(u, body);
			for (ConditionalExceptionContainer ce : entry.getValue()) {
				Trap trap = null;
				List<Trap> relevantTraps = new LinkedList<Trap>();

				/*
				 * if the current exception is created from a throws clause of a
				 * method invoke, we need special handling, because the thrown
				 * exception might as well be a sub type of the declared one, in
				 * which case a different trap might catch it.
				 */
				if (u instanceof InvokeStmt && ce.getValue() == null
						&& ((InvokeStmt) u).getInvokeExpr().getMethod().getExceptions().contains(ce.getException())) {
					for (Trap t : possibleTraps) {
						// Check if the exception is either a sub-class or a
						// super-class.
						if (h.isClassSubclassOfIncluding(t.getException(), ce.getException())
								|| h.isClassSubclassOfIncluding(ce.getException(), t.getException())) {
							// check if we already have a trap for this
							// exception
							// then the other trap is unreachable.
							boolean foundInPrevious = false;
							for (Trap previous : relevantTraps) {
								//Check if we already have a trap for this class (or a super class).
								if (h.isClassSubclassOfIncluding(t.getException(), previous.getException())) {
									foundInPrevious = true;
									break;
								}
							}
							if (!foundInPrevious) {
								relevantTraps.add(t);
							}
							trap = t;
							//Check if t is already of type ce.getException() or a super
							//type of it. In this case, we are done.
							if (h.isClassSubclassOfIncluding(ce.getException(), t.getException())) {
								break;
							}
						}

					}
				} else {
					// find the first trap that catches this exception.
					for (Trap t : possibleTraps) {
						if (h.isClassSubclassOfIncluding(ce.getException(), t.getException())) {
							trap = t;
							relevantTraps.add(t);
							break;
						}
					}
				}

				if (trap != null) {
					handleCaughtException(body, u, ce, relevantTraps);
				} else {
					// check if the exception is declared in throws-clause
					SootClass inThrowsClause = null;
					for (SootClass sc : body.getMethod().getExceptions()) {
						if (h.isClassSubclassOfIncluding(ce.getException(), sc)) {
							inThrowsClause = sc;
						}
					}
					if (inThrowsClause != null) {
						handleDeclaredException(body, u, ce, inThrowsClause);
					} else {
						handleUndeclaredException(body, u, ce);
					}
				}
			}

		}

		body.validate();
	}

	/**
	 * Handle an exception that has a catch block
	 * 
	 * @param b
	 *            Body of the procedure
	 * @param u
	 *            The unit that throws the exception
	 * @param ce
	 *            The ConditionalException
	 * @param t
	 *            The trap that catches this exception
	 */
	protected void handleCaughtException(Body b, Unit u, ConditionalExceptionContainer ce, List<Trap> traps) {
		List<Pair<Value, List<Unit>>> guards = constructGuardExpression(b, ce, true, u);
		Map<Trap, Unit> createExceptionMap = new HashMap<Trap, Unit>();
		for (Trap t : traps) {
			// add a block that creates an exception object
			// and assigns it to $exception.
			if (!caughtExceptionLocal.containsKey(t)) {
				// only create one local per trap so that we can
				// replace the CaughtExceptionRef later.
				caughtExceptionLocal.put(t, getFreshLocal(b, exceptionVariable.getType()));
			}
			Local execptionLocal = caughtExceptionLocal.get(t);
			List<Unit> excCreation = createNewException(b, execptionLocal, ce.getException(), u);
			createExceptionMap.put(t, excCreation.get(0));
			excCreation.add(gotoStmtFor(t.getHandlerUnit(), u));
			b.getUnits().addAll(excCreation);
		}

		if (guards != null) {
			// if this is RuntimeException that is not raised by a call
			// there can only be one trap.
			assert(traps.size() == 1);
			Trap t = traps.get(0);
			// now create the conditional jump to the trap.
			for (Pair<Value, List<Unit>> pair : guards) {
				List<Unit> toInsert = new LinkedList<Unit>();
				toInsert.addAll(pair.getSecond());
				toInsert.add(ifStmtFor(pair.getFirst(), createExceptionMap.get(t), u));
				b.getUnits().insertBefore(toInsert, u);
			}
		} else {
			// This is only the case for procedures calls that may throw an
			// exception.
			// In that case, we have to insert the exception handling after the
			// statement.
			// Note that there also might be multiple traps since we don't
			// know if the procedure throws a sub-type of the declared
			// exception.
			List<Unit> toInsert = new LinkedList<Unit>();
			for (Trap t : traps) {
				// l := $exceptionVariable instanceof t.getException
				Local l = getFreshLocal(b, IntType.v());
				toInsert.add(assignStmtFor(l,
						Jimple.v().newInstanceOfExpr(exceptionVariable, t.getException().getType()), u));
				toInsert.add(ifStmtFor(jimpleNeZero(l), createExceptionMap.get(t), u));
			}
			b.getUnits().insertAfter(toInsert, u);
		}
		for (Trap t : traps) {
			// Replace the caughtExceptionRef in the handler unit by
			// the exception local so that we can remove the traps.
			// For that we also need to add assignments that assign the
			// exception
			// variable to the corresponding new exception.
			if (t.getHandlerUnit() instanceof DefinitionStmt) {
				DefinitionStmt ds = (DefinitionStmt) t.getHandlerUnit();
				if (ds.getRightOp() instanceof CaughtExceptionRef) {
					Unit newAssign = assignStmtFor(ds.getLeftOp(), caughtExceptionLocal.get(t), u);
					b.getUnits().insertAfter(newAssign, ds);
					b.getUnits().remove(ds);
				}
			} else {
				throw new RuntimeException("Unexpected " + t.getHandlerUnit());
			}
		}
	}

	private Map<SootClass, Unit> generatedThrowStatements = new HashMap<SootClass, Unit>();
	private Map<Trap, Local> caughtExceptionLocal = new HashMap<Trap, Local>();

	/**
	 * Handle an exception that has no catch block but is declared in the
	 * procedures throws clause.
	 * 
	 * @param b
	 *            Body of the procedure
	 * @param u
	 *            The unit that throws the exception
	 * @param ce
	 *            The ConditionalException
	 * @param tc
	 *            The class in the throws clause
	 */
	protected void handleDeclaredException(Body b, Unit u, ConditionalExceptionContainer ce, SootClass tc) {
		List<Pair<Value, List<Unit>>> guards = constructGuardExpression(b, ce, true, u);
		if (!generatedThrowStatements.containsKey(ce.getException())) {
			List<Unit> exc = throwNewException(b, ce.getException(), u);
			Unit newException = exc.get(0);
			b.getUnits().addAll(exc);
			generatedThrowStatements.put(ce.getException(), newException);
		}
		Unit throwStmt = generatedThrowStatements.get(ce.getException());

		if (guards != null) {
			for (Pair<Value, List<Unit>> pair : guards) {

				List<Unit> toInsert = new LinkedList<Unit>();
				toInsert.addAll(pair.getSecond());
				toInsert.add(ifStmtFor(pair.getFirst(), throwStmt, u));

				b.getUnits().insertBefore(toInsert, u);
			}
		} else {
			// This is only the case for procedures calls that may throw an
			// exception.
			// In that case, we have to insert the exception handling after the
			// statement.
			List<Unit> toInsert = new LinkedList<Unit>();
			// l := $exceptionVariable instanceof t.getException
			Local l = getFreshLocal(b, IntType.v());
			toInsert.add(assignStmtFor(l, Jimple.v().newInstanceOfExpr(exceptionVariable, tc.getType()), u));
			toInsert.add(ifStmtFor(jimpleNeZero(l), throwStmt, u));
			b.getUnits().insertAfter(toInsert, u);
		}
	}

	/**
	 * Handle an exception that is neither caught nor declared in the throws
	 * clause.
	 * 
	 * @param b
	 * @param u
	 * @param ce
	 */
	protected void handleUndeclaredException(Body b, Unit u, ConditionalExceptionContainer ce) {
		List<Pair<Value, List<Unit>>> guards = constructGuardExpression(b, ce, false, u);
		if (guards != null) {
			// now create the conditional jump to the trap.
			for (Pair<Value, List<Unit>> pair : guards) {
				List<Unit> toInsert = new LinkedList<Unit>();
				toInsert.addAll(pair.getSecond());
				// assert guard
				Local l = getFreshLocal(b, BooleanType.v());
				toInsert.add(assignStmtFor(l, pair.getFirst(), u));
				toInsert.add(
						Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(internalAssertMethod.makeRef(), l)));
				b.getUnits().insertBefore(toInsert, u);
			}
		} else {
			// This is only the case for procedures calls that may throw an
			// exception that is a sub-type of RuntimeException.
			// Otherwise, the exception either has to be caught or add to the
			// throws clause of this method.
			// In that case, we have to insert the exception handling after the
			// statement.

			// TODO: emit a warning here because this is kind of dangerous.
			List<Unit> toInsert = new LinkedList<Unit>();
			// l := $exceptionVariable instanceof t.getException
			// c := l == 0
			// assert c
			Local l = getFreshLocal(b, IntType.v());
			toInsert.add(
					assignStmtFor(l, Jimple.v().newInstanceOfExpr(exceptionVariable, ce.getException().getType()), u));
			Local cond = getFreshLocal(b, IntType.v());
			toInsert.add(assignStmtFor(cond, jimpleEqZero(l), u));
			toInsert.add(
					Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(internalAssertMethod.makeRef(), cond)));
			b.getUnits().insertAfter(toInsert, u);
		}

	}

	protected List<Unit> createNewException(Body b, Local exLocal, SootClass exc, Host createdFrom) {
		List<Unit> result = new LinkedList<Unit>();
		/*
		 * generate l := new Exception constructor call throw l
		 */
		Local l = exLocal;
		// l = new Exception
		Unit newException = assignStmtFor(l, Jimple.v().newNewExpr(RefType.v(exc)), createdFrom);
		result.add(newException);
		// constructor call
		for (SootMethod sm : exc.getMethods()) {
			if (sm.isConstructor() && sm.getParameterCount() == 0) {
				// This is the constructor we are looking for.
				result.add(invokeStmtFor(Jimple.v().newSpecialInvokeExpr(l, sm.makeRef()), createdFrom));
				break;
			}
		}
		return result;
	}

	protected List<Unit> throwNewException(Body b, SootClass exc, Host createdFrom) {
		List<Unit> result = createNewException(b, exceptionVariable, exc, createdFrom);
		result.add(throwStmtFor(exceptionVariable, createdFrom));
		return result;
	}

	/**
	 * Generates for a given ConditionalExceptionContainer a list of pairs of
	 * the Value under which the exception occurs (or the negated version if
	 * negated is true), and the list of supporting statements, such as temp
	 * variables.
	 * 
	 * In most cases, the list contains only one element. Only for
	 * IndexOutOfBoundsExceptions it returns two elements. One checking the
	 * lower bound and one checking the upper bound. This is because Jimple does
	 * not have disjunctions.
	 * 
	 * @param body
	 *            The current body
	 * @param ce
	 *            ConditionalExceptionContainer
	 * @param negated
	 *            If the conditions should be negated.
	 * @return List of pairs
	 */
	protected List<Pair<Value, List<Unit>>> constructGuardExpression(Body body, ConditionalExceptionContainer ce,
			boolean negated, Host createdFrom) {
		List<Pair<Value, List<Unit>>> result = new LinkedList<Pair<Value, List<Unit>>>();
		if (ce.value == null) {
			// that is, the exception came from the throws clause of a function.
			return null;
		} else if (ce.exception == nulLPointerExceptionClass) {
			// no helper statements needed.
			if (negated) {
				result.add(new Pair<Value, List<Unit>>(Jimple.v().newEqExpr(ce.getValue(), NullConstant.v()),
						new LinkedList<Unit>()));
			} else {
				result.add(new Pair<Value, List<Unit>>(Jimple.v().newNeExpr(ce.getValue(), NullConstant.v()),
						new LinkedList<Unit>()));
			}
			return result;
		} else if (ce.exception == arrayIndexOutOfBoundsExceptionClass) {
			ArrayRef e = (ArrayRef) ce.getValue();
			// index < array.length
			/*
			 * Since array.length cannot be part of a BinOp, we have to create a
			 * helper local l and a statement l = array.length first.
			 */
			List<Unit> helperStatements = new LinkedList<Unit>();
			Local len = getFreshLocal(body, IntType.v());
			Unit helperStmt = assignStmtFor(len, Jimple.v().newLengthExpr(e.getBase()), createdFrom);
			helperStatements.add(helperStmt);

			Local left = getFreshLocal(body, IntType.v());
			helperStmt = assignStmtFor(left, Jimple.v().newLtExpr(e.getIndex(), len), createdFrom);
			helperStatements.add(helperStmt);
			// !(index < array.length)
			if (negated) {
				result.add(new Pair<Value, List<Unit>>(jimpleEqZero(left), helperStatements));
			} else {
				result.add(new Pair<Value, List<Unit>>(jimpleNeZero(left), helperStatements));
			}

			// index >= 0
			helperStatements = new LinkedList<Unit>();
			Local right = getFreshLocal(body, IntType.v());
			helperStmt = assignStmtFor(right, Jimple.v().newGeExpr(e.getIndex(), IntConstant.v(0)), createdFrom);
			helperStatements.add(helperStmt);
			// !(index>=0)
			if (negated) {
				result.add(new Pair<Value, List<Unit>>(jimpleEqZero(right), helperStatements));
			} else {
				result.add(new Pair<Value, List<Unit>>(jimpleNeZero(right), helperStatements));
			}

			return result;

		} else if (ce.exception == classCastExceptionClass) {
			CastExpr e = (CastExpr) ce.getValue();
			// e instanceof t
			/*
			 * Since instanceof cannot be part of a UnOp, we have to create a
			 * helper local l and a statement l = e instanceof t first.
			 */
			List<Unit> helperStatements = new LinkedList<Unit>();
			Local helperLocal = getFreshLocal(body, IntType.v());
			Unit helperStmt = assignStmtFor(helperLocal, Jimple.v().newInstanceOfExpr(e.getOp(), e.getCastType()),
					createdFrom);
			helperStatements.add(helperStmt);
			if (negated) {
				result.add(new Pair<Value, List<Unit>>(jimpleEqZero(helperLocal), helperStatements));
			} else {
				result.add(new Pair<Value, List<Unit>>(jimpleNeZero(helperLocal), helperStatements));
			}
			return result;
		}
		throw new RuntimeException("not implemented");
	}

	private List<ConditionalExceptionContainer> collectPossibleExceptions(Unit u) {
		List<ConditionalExceptionContainer> result = new LinkedList<ConditionalExceptionContainer>();
		if (u instanceof DefinitionStmt) {
			DefinitionStmt s = (DefinitionStmt) u;
			// precedence says left before right.
			result.addAll(collectPossibleExceptions(u, s.getLeftOp()));
			result.addAll(collectPossibleExceptions(u, s.getRightOp()));

		} else if (u instanceof SwitchStmt) {
			SwitchStmt s = (SwitchStmt) u;
			result.addAll(collectPossibleExceptions(u, s.getKey()));
		} else if (u instanceof IfStmt) {
			IfStmt s = (IfStmt) u;
			result.addAll(collectPossibleExceptions(u, s.getCondition()));
		} else if (u instanceof InvokeStmt) {
			InvokeStmt s = (InvokeStmt) u;
			if (s instanceof InstanceInvokeExpr) {
				result.addAll(collectPossibleExceptions(u, ((InstanceInvokeExpr) s).getBase()));
			}
			for (Value v : s.getInvokeExpr().getArgs()) {
				result.addAll(collectPossibleExceptions(u, v));
			}
			// handle the exceptions in the throws clause.
			for (SootClass sc : s.getInvokeExpr().getMethod().getExceptions()) {
				result.add(new ConditionalExceptionContainer(null, sc));
			}
		} else if (u instanceof ReturnStmt) {
			ReturnStmt s = (ReturnStmt) u;
			result.addAll(collectPossibleExceptions(u, s.getOp()));
		} else if (u instanceof ThrowStmt) {
			ThrowStmt s = (ThrowStmt) u;
			result.addAll(collectPossibleExceptions(u, s.getOp()));
		}
		return result;
	}

	private List<ConditionalExceptionContainer> collectPossibleExceptions(Unit u, Value v) {
		List<ConditionalExceptionContainer> result = new LinkedList<ConditionalExceptionContainer>();
		if (v instanceof BinopExpr) {
			BinopExpr e = (BinopExpr) v;
			// precedence says left before right.
			result.addAll(collectPossibleExceptions(u, e.getOp1()));
			result.addAll(collectPossibleExceptions(u, e.getOp2()));
		} else if (v instanceof UnopExpr) {
			UnopExpr e = (UnopExpr) v;
			result.addAll(collectPossibleExceptions(u, e.getOp()));
		} else if (v instanceof InvokeExpr) {
			if (v instanceof InstanceInvokeExpr) {
				result.addAll(collectPossibleExceptions(u, ((InstanceInvokeExpr) v).getBase()));
			}
			for (int i = 0; i < ((InvokeExpr) v).getArgCount(); i++) {
				result.addAll(collectPossibleExceptions(u, ((InvokeExpr) v).getArg(i)));
			}
		} else if (v instanceof CastExpr) {
			CastExpr e = (CastExpr) v;
			result.addAll(collectPossibleExceptions(u, e.getOp()));
			ConditionalExceptionContainer ce = new ConditionalExceptionContainer(v, classCastExceptionClass);
			result.add(ce);
		} else if (v instanceof InstanceOfExpr) {
			InstanceOfExpr e = (InstanceOfExpr) v;
			result.addAll(collectPossibleExceptions(u, e.getOp()));
		} else if (v instanceof Ref) {
			result.addAll(refMayThrowException(u, (Ref) v));
		} else if (v instanceof AnyNewExpr || v instanceof Immediate) {
			// ignore
		} else {
			throw new RuntimeException("Not handling " + v + " of type " + v.getClass());
		}

		return result;
	}

	private List<ConditionalExceptionContainer> refMayThrowException(Unit u, Ref r) {
		List<ConditionalExceptionContainer> result = new LinkedList<ConditionalExceptionContainer>();
		if (r instanceof InstanceFieldRef) {
			InstanceFieldRef e = (InstanceFieldRef) r;
			result.addAll(collectPossibleExceptions(u, e.getBase()));
			if (e.getBase() instanceof Immediate
					&& nullnessAnalysis.isAlwaysNonNullBefore(u, (Immediate) e.getBase())) {
				// no need to add null pointer check.
			} else {
				ConditionalExceptionContainer ce = new ConditionalExceptionContainer(e.getBase(),
						nulLPointerExceptionClass);
				result.add(ce);
			}
		} else if (r instanceof ArrayRef) {
			ArrayRef e = (ArrayRef) r;
			result.addAll(collectPossibleExceptions(u, e.getBase()));
			result.addAll(collectPossibleExceptions(u, e.getIndex()));
			ConditionalExceptionContainer ce = new ConditionalExceptionContainer(e,
					arrayIndexOutOfBoundsExceptionClass);
			result.add(ce);
		} else if (r instanceof IdentityRef || r instanceof StaticFieldRef) {
			// do nothing.
		}
		return result;
	}

	/**
	 * Helper class to represent conditional exceptions that may be thrown by a
	 * Value.
	 * 
	 * @author schaef
	 */
	protected static class ConditionalExceptionContainer {
		private final Value value;
		private final SootClass exception;

		public ConditionalExceptionContainer(Value c, SootClass ex) {
			value = c;
			exception = ex;
		}

		public Value getValue() {
			return value;
		}

		public SootClass getException() {
			return exception;
		}
	}

	/**
	 * Get the list of all traps that may catch exceptions thrown by u.
	 * 
	 * @param u
	 * @param b
	 * @return
	 */
	protected List<Trap> getTrapsGuardingUnit(Unit u, Body b) {
		List<Trap> result = new LinkedList<Trap>();
		for (Trap t : b.getTraps()) {
			Iterator<Unit> it = b.getUnits().iterator(t.getBeginUnit(), t.getEndUnit());
			while (it.hasNext()) {
				if (u.equals(it.next())) {
					result.add(t);
				}
			}
		}
		return result;
	}

}
