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
import soot.BodyTransformer;
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
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.AnyNewExpr;
import soot.jimple.ArrayRef;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
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
import soottocfg.util.Pair;

/**
 * @author schaef
 *
 */
public class ExceptionTransformer extends BodyTransformer {

	private NullnessAnalysis nullnessAnalysis;
	protected final SootClass exceptionClass, nulLPointerExceptionClass, indexOutOfBoundsExceptionClass, classCastExceptionClass;
	
	protected Local exceptionVariable;
	private final SootMethod internalAssertMethod;
	
	/**
	 * 
	 */
	public ExceptionTransformer(NullnessAnalysis nna) {
		nullnessAnalysis = nna;		
		exceptionClass = Scene.v().getSootClass("java.lang.Exception");
		nulLPointerExceptionClass = Scene.v().getSootClass("java.lang.NullPointerException");
		indexOutOfBoundsExceptionClass = Scene.v().getSootClass("java.lang.IndexOutOfBoundsException");
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
		Map<Unit,List<ConditionalExceptionContainer>> needsHandling = new HashMap<Unit,List<ConditionalExceptionContainer>>();

		exceptionVariable = Jimple.v().newLocal("$exception", RefType.v(exceptionClass));
		body.getLocals().add(exceptionVariable);
		
		Hierarchy h = Scene.v().getActiveHierarchy();
		
		PatchingChain<Unit> units = body.getUnits();
		for (Unit u : units) {			
			List<ConditionalExceptionContainer> result =  collectPossibleExceptions(u);
			if (!result.isEmpty()) {
				needsHandling.put(u, result);
			}			
		}
		
		for (Entry<Unit,List<ConditionalExceptionContainer>> entry : needsHandling.entrySet()) {
			Unit u = entry.getKey();
			List<Trap> possibleTraps = getTrapsGuardingUnit(u, body);			
			for (ConditionalExceptionContainer ce : entry.getValue()) {
				Trap trap = null;
				for (Trap t : possibleTraps) {
					if (h.isClassSubclassOfIncluding(t.getException(), ce.getException())) {
						trap = t;
						break;
					}
				}
				if (trap!=null) {
					handleCaughtException(body, u, ce, trap);
				} else {
					//check if the exception is declared in throws-clause
					SootClass inThrowsClause = null;
					for (SootClass sc : body.getMethod().getExceptions()) {
						if (h.isClassSubclassOfIncluding(sc, ce.getException())) {
							inThrowsClause = sc;
						}
					}
					if (inThrowsClause!=null) {
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
	 * @param b Body of the procedure
	 * @param u The unit that throws the exception 
	 * @param ce The ConditionalException
	 * @param t The trap that catches this exception
	 */
	protected void handleCaughtException(Body b, Unit u, ConditionalExceptionContainer ce, Trap t) {
		List<Pair<Value, List<Unit>>> guards = constructGuardExpression(b, ce, true);
		if (guards !=null) {
			//now create the conditional jump to the trap.			
			for (Pair<Value, List<Unit>> pair : guards) {
				List<Unit> toInsert = new LinkedList<Unit>();
				toInsert.addAll(pair.getSecond());
				toInsert.add(Jimple.v().newIfStmt(pair.getFirst(), t.getHandlerUnit()));
				b.getUnits().insertBefore(toInsert, u);
			}
		} else {
			//This is only the case for procedures calls that may throw an exception.
			//In that case, we have to insert the exception handling after the statement.
			//TODO:
		}
	}

	private Map<SootClass, Unit> generatedThrowStatements = new HashMap<SootClass, Unit>();
	
	/**
	 * Handle an exception that has no catch block
	 * but is declared in the procedures throws clause.
	 * @param b Body of the procedure
	 * @param u The unit that throws the exception
	 * @param ce The ConditionalException
	 * @param tc The class in the throws clause
	 */
	protected void handleDeclaredException(Body b, Unit u, ConditionalExceptionContainer ce, SootClass tc) {
		List<Pair<Value, List<Unit>>> guards = constructGuardExpression(b, ce, true);
		if (guards !=null) {
			for (Pair<Value, List<Unit>> pair : guards) {
				if (!generatedThrowStatements.containsKey(ce.getException())) {
					Unit throwStmt = Jimple.v().newThrowStmt(Jimple.v().newNewExpr(RefType.v(ce.getException()))); 
					b.getUnits().add(throwStmt);
					generatedThrowStatements.put(ce.getException(),  throwStmt);
				}
				Unit throwStmt =  generatedThrowStatements.get(ce.getException());
								
				List<Unit> toInsert = new LinkedList<Unit>();
				toInsert.addAll(pair.getSecond());
				toInsert.add(Jimple.v().newIfStmt(pair.getFirst(), throwStmt));
				
				b.getUnits().insertBefore(toInsert, u);				
			}
		} else {
			//This is only the case for procedures calls that may throw an exception.
			//In that case, we have to insert the exception handling after the statement.
			
		}
	}	
	
	/**
	 * Handle an exception that is neither caught
	 * nor declared in the throws clause.
	 * @param b
	 * @param u
	 * @param ce
	 */
	protected void handleUndeclaredException(Body b, Unit u, ConditionalExceptionContainer ce) {
		List<Pair<Value, List<Unit>>> guards = constructGuardExpression(b, ce, false);
		if (guards !=null) {
			//now create the conditional jump to the trap.			
			for (Pair<Value, List<Unit>> pair : guards) {
				List<Unit> toInsert = new LinkedList<Unit>();
				toInsert.addAll(pair.getSecond());
				//assert guard
				Local l = getFreshLocal(b, BooleanType.v());
				toInsert.add(Jimple.v().newAssignStmt(l, pair.getFirst()));
				toInsert.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(internalAssertMethod.makeRef(), l)));
				b.getUnits().insertBefore(toInsert, u);
			}
		} else {
			//This is only the case for procedures calls that may throw an exception.
			//In that case, we have to insert the exception handling after the statement.
			
		}

	}
	
	

	/**
	 * TODO
	 * @param body
	 * @param ce
	 * @param negated
	 * @return
	 */
	protected List<Pair<Value, List<Unit>>> constructGuardExpression(Body body, ConditionalExceptionContainer ce, boolean negated) {
		List<Pair<Value, List<Unit>>> result = new LinkedList<Pair<Value, List<Unit>>>();
		if (ce.value==null) {
			//that is, the exception came from the throws clause of a function.
			return null;
		} else if (ce.exception == nulLPointerExceptionClass) {
			//no helper statements needed.
			if (negated) {
				result.add(new Pair<Value,List<Unit>>(Jimple.v().newEqExpr(ce.getValue(), NullConstant.v()), new LinkedList<Unit>()));
			} else {
				result.add(new Pair<Value,List<Unit>>(Jimple.v().newNeExpr(ce.getValue(), NullConstant.v()), new LinkedList<Unit>()));
			}
			return result;
		} else if (ce.exception == indexOutOfBoundsExceptionClass) {
			ArrayRef e = (ArrayRef)ce.getValue();
			//index < array.length
			/*
			 * Since array.length cannot be part of a BinOp, 
			 * we have to create a helper local l and a statement
			 * l = array.length
			 * first. 
			 */
			List<Unit> helperStatements = new LinkedList<Unit>();
			Local len = getFreshLocal(body, IntType.v());
			Unit helperStmt = Jimple.v().newAssignStmt(len, Jimple.v().newLengthExpr(e.getBase()));
			helperStatements.add(helperStmt);			

			Local left = getFreshLocal(body, IntType.v());			
			helperStmt = Jimple.v().newAssignStmt(left, Jimple.v().newLtExpr(e.getIndex(), len));
			helperStatements.add(helperStmt);
			//!(index < array.length)
			if (negated) {
				result.add(new Pair<Value, List<Unit>>(jimpleEqZero(left), helperStatements));
			} else {
				result.add(new Pair<Value, List<Unit>>(jimpleNeZero(left), helperStatements));
			}
			
			//index >= 0
			helperStatements = new LinkedList<Unit>();
			Local right = getFreshLocal(body, IntType.v());
			helperStmt = Jimple.v().newAssignStmt(right, Jimple.v().newGeExpr(e.getIndex(), IntConstant.v(0)));
			helperStatements.add(helperStmt);
			//!(index>=0)
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
			 * Since instanceof cannot be part of a UnOp, 
			 * we have to create a helper local l and a statement
			 * l = e instanceof t
			 * first. 
			 */			
			List<Unit> helperStatements = new LinkedList<Unit>();
			Local helperLocal = getFreshLocal(body, IntType.v());			
			Unit helperStmt = Jimple.v().newAssignStmt(helperLocal, Jimple.v().newInstanceOfExpr(e.getOp(), e.getCastType()));
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
	
	private Value jimpleEqZero(Value v) {
		return Jimple.v().newEqExpr(v, IntConstant.v(0));
	}

	private Value jimpleNeZero(Value v) {
		return Jimple.v().newNeExpr(v, IntConstant.v(0));
	}

	
	private long counter = 0;
	protected Local getFreshLocal(Body body, Type t) {
		Local local = Jimple.v().newLocal("$helper"+(counter++), t);
		body.getLocals().add(local);
		return local;
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
				result.addAll(collectPossibleExceptions(u, ((InstanceInvokeExpr)s).getBase()));
			}
			for (Value v : s.getInvokeExpr().getArgs()) {
				result.addAll(collectPossibleExceptions(u, v));
			}
			//handle the exceptions in the throws clause.
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
			ConditionalExceptionContainer ce = new ConditionalExceptionContainer(v,
					classCastExceptionClass);
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
					indexOutOfBoundsExceptionClass);
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
