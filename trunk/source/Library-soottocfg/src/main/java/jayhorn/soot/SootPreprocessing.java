/**
 * 
 */
package jayhorn.soot;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import jayhorn.util.Log;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.Local;
import soot.Modifier;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.VoidType;
import soot.jimple.AssignStmt;
import soot.jimple.ClassConstant;
import soot.jimple.GotoStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeStmt;
import soot.jimple.Jimple;
import soot.jimple.NewExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;

/**
 * @author schaef
 *
 */
public enum SootPreprocessing {
	INSTANCE;

	public static SootPreprocessing v() {
		return INSTANCE;
	}

	/*
	 * Code to handle Java Assertions.
	 */
	private static final String assertionClassName = "JayHornAssertions";
	private static final String assertionProcedureName = "super_crazy_assertion";

	private static final String javaAssertionType = "java.lang.AssertionError";
	private static final String javaAssertionFlag = "$assertionsDisabled";
		
	private SootMethod internalAssertMethod = null;
	
	/**
	 * Initialize the helper classes and methods that
	 * we use when pre-processing soot.
	 * This has to be done in SootToCfg before we iterate
	 * over the classes to avoid concurrent modification 
	 * error from the Scene.
	 */
	public void initialize() {
		if (internalAssertMethod==null) {
			SootClass sClass = new SootClass(assertionClassName, Modifier.PUBLIC);			
			internalAssertMethod = new SootMethod(assertionProcedureName,                 
				    Arrays.asList(new Type[] {ArrayType.v(BooleanType.v(), 1)}),
				    VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);			
			sClass.addMethod(internalAssertMethod);
			
			Scene.v().addClass(sClass);
		}				
	}
	
	public SootMethod getAssertMethod() {
		return internalAssertMethod;
	}

	/**
	 * removes useless statements that are generated when
	 * java assertions are translated into bytecode.
	 * @param body
	 */
	public void removeAssertionRelatedNonsense(Body body) {
		/*
		 * Look for the following sequence and remove it.
	        $r0 = class "translation_tests/TranslationTest01";
	        $z0 = virtualinvoke $r0.<java.lang.Class: boolean desiredAssertionStatus()>();
	        if $z0 != 0 goto label1;
	        $z1 = 1;
	(0)     goto label2;
	     label1:
	(1)     $z1_1 = 0;
	     label2:
	        <translation_tests.TranslationTest01: boolean $assertionsDisabled> = $z1_2;
		 */
		Set<Unit> unitsToRemove = new HashSet<Unit>();
		Iterator<Unit> iterator = body.getUnits().iterator();
		while (iterator.hasNext()) {
			Unit u = iterator.next();
			if (u instanceof AssignStmt) {
				AssignStmt asgn = (AssignStmt)u;
				if (asgn.getLeftOp() instanceof Local && asgn.getRightOp() instanceof ClassConstant) {
					ClassConstant rhs = (ClassConstant)asgn.getRightOp();
					final String c = body.getMethod().getDeclaringClass().getName().replace('.', '/');
					//search for $r0 = class "translation_tests/TranslationTest01";
					if (rhs.getValue().equals(c)) {
						unitsToRemove.add(u);
						final int lookAhead = 6;
						Stmt[] uslessBlock = new Stmt[lookAhead];
						for (int i=0;i<lookAhead;i++) {
							if (!iterator.hasNext()) {
								unitsToRemove.clear();
								break;
							}
							uslessBlock[i] = (Stmt)iterator.next();
							unitsToRemove.add(uslessBlock[i]);
						}
						
						//$z0 = virtualinvoke $r0.<java.lang.Class: boolean desiredAssertionStatus()>();
						if (!uslessBlock[0].containsInvokeExpr() || !uslessBlock[0].getInvokeExpr().getMethod().getName().equals("desiredAssertionStatus")) {
							unitsToRemove.clear();
							continue;							
						}
				        
				        //if $z0 != 0 goto label1;
				        if (!(uslessBlock[1] instanceof IfStmt) || ((IfStmt)uslessBlock[1]).getTarget()!=uslessBlock[4]) {
							unitsToRemove.clear();
							continue;				        	
				        }
						//$z1 = 1;
				        if (!(uslessBlock[2] instanceof AssignStmt) || !((AssignStmt)uslessBlock[2]).getRightOp().toString().equals("1")) {
							unitsToRemove.clear();
							continue;				        					        	
				        }
						//goto label2;
				        if (!(uslessBlock[3] instanceof GotoStmt) || ((GotoStmt)uslessBlock[3]).getTarget()!=uslessBlock[5]) {
							unitsToRemove.clear();
							continue;				        					        					        	
				        }
						//$z1_1 = 0;
				        if (!(uslessBlock[4] instanceof AssignStmt) || !((AssignStmt)uslessBlock[4]).getRightOp().toString().equals("0")) {
							unitsToRemove.clear();
							continue;				        					        	
				        }
				        //<translation_tests.TranslationTest01: boolean $assertionsDisabled> = $z1_2;
				        if (!(uslessBlock[5] instanceof AssignStmt) || !((AssignStmt)uslessBlock[5]).getLeftOp().toString().contains("$assertionsDisabled")) {
							unitsToRemove.clear();
							continue;				        					        					        					        	
				        }
				        //we found the block.
				        break;
					}
				}
			}
		}
		if (!unitsToRemove.isEmpty()) {
			Log.info("removed useless block in "+body.getMethod().getBytecodeSignature());
			body.getUnits().removeAll(unitsToRemove);
			body.validate();
		}
	}
	
	/**
	 * Look for parts of the body that have been created from Java
	 * assert statements. These are always of the form:
	 * 
	 *  $z0 = <Assert: boolean $assertionsDisabled>;
     *  if $z0 != 0 goto label1;
     *  [[some statements]]
     *  if [[some condition]] goto label1;
     *  $r1 = new java.lang.AssertionError;
     *  specialinvoke $r1.<java.lang.AssertionError: void <init>()>();
     *  throw $r1; 
     *  
     *  and replace those blocks by:
     *  [[some statements]]
     *  $assert_condition = [[some condition]];
     *  staticinvoke <JayHornAssertions: void super_crazy_assertion(boolean[])>($assert_condition);
     *  
	 * @param body
	 */
	public void reconstructJavaAssertions(Body body) {
		Set<Unit> unitsToRemove = new HashSet<Unit>();
		Map<Unit, Value> assertionsToInsert = new HashMap<Unit,Value>();

//		body.getUnits().insertAfter(toInsert, point);
		Iterator<Unit> iterator = body.getUnits().iterator();
		while (iterator.hasNext()) {
			Unit u = iterator.next();
			if (isSootAssertionFlag(u)) {
				//u := $z0 = <Assert: boolean $assertionsDisabled>;
				unitsToRemove.add(u);
				//u := if $z0 != 0 goto label1;
				u = iterator.next();
				if (!(u instanceof IfStmt)) {
					throw new RuntimeException("");
				}
				unitsToRemove.add(u);
				
				//now search for the new java.lang.AssertionError
				Unit previousUnit = null;
				while (iterator.hasNext()) {
					u = iterator.next();
					if (isNewJavaAssertionError(u)) {
						//u := $r1 = new java.lang.AssertionError;
						unitsToRemove.add(u);
						//the statement before should be 
						//the expression from the java assertion
						// previousUnit := if $i0 != 5 goto label1;
						if (!(previousUnit instanceof IfStmt)) {
							if (previousUnit==null) {
								//then this is an assert(false) statement.								
								assertionsToInsert.put(u, IntConstant.v(0));
							} else {
								throw new RuntimeException("Assertion reconstruction broken");
							}
						} else {						
							unitsToRemove.add(previousUnit);
							IfStmt ite = (IfStmt)previousUnit;						
							assertionsToInsert.put(u, ite.getCondition());
						}
						break;
					}
					previousUnit = u;
				}
				//u :=  specialinvoke $r1.<java.lang.AssertionError: void <init>()>();
				u = iterator.next();			     
				if (!(u instanceof InvokeStmt)) {
					throw new RuntimeException(u.toString());
				}
				unitsToRemove.add(u);
				
				// u :=  throw $r1;
				u = iterator.next();			    
				if (!(u instanceof ThrowStmt)) {
					throw new RuntimeException(u.toString());
				}
				unitsToRemove.add(u);
				
				continue;
			} 			
		}
		Local assertionLocal = null;
		if (!assertionsToInsert.isEmpty()) {
			assertionLocal = Jimple.v().newLocal("$assert_condition", BooleanType.v());
			body.getLocals().add(assertionLocal);
		}
		//remove all boilerplate statements
		//generated from the assertions.				
		for (Entry<Unit, Value> entry : assertionsToInsert.entrySet()) {
			List<Unit> unitsToInsert = new LinkedList<Unit>();
			List<Value> args = new LinkedList<Value>();
			args.add(assertionLocal);
			unitsToInsert.add(Jimple.v().newAssignStmt(assertionLocal, entry.getValue()));
			unitsToInsert.add(Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(internalAssertMethod.makeRef(), args)));			

			body.getUnits().insertBefore(unitsToInsert, entry.getKey());
			unitsToRemove.add(entry.getKey());
		}
		
		body.getUnits().removeAll(unitsToRemove);
		body.validate();
	}
		
	/**
	 * Checks if u has been created from a Java assert statement
	 * and is of the form:
	 * $r1 = new java.lang.AssertionError;
	 * @param u
	 * @return
	 */
	private boolean isNewJavaAssertionError(Unit u) {
		if (u instanceof AssignStmt) {
			AssignStmt ids = (AssignStmt)u;
			if (ids.getRightOp() instanceof NewExpr) {
				NewExpr ne = (NewExpr)ids.getRightOp();
				return ne.getType().toString().equals(javaAssertionType);
			}
		}				
		return false;
	}
	
	/**
	 * Checks if u has been created from a Java assert statement
	 * and is of the form:
	 * $z0 = <Assert: boolean $assertionsDisabled>;
	 * @param u
	 * @return
	 */
	private boolean isSootAssertionFlag(Unit u) {
		if (u instanceof AssignStmt) {
			AssignStmt ids = (AssignStmt)u;
			if (ids.getRightOp() instanceof StaticFieldRef) {
				StaticFieldRef sfr = (StaticFieldRef)ids.getRightOp();
				return sfr.getField().getName().equals(javaAssertionFlag);
			}
		}		
		return false;
	}
		
	
}
