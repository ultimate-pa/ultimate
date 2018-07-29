package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination;

import static de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils.allVariablesAreVisible;
import static de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils.translateTermVariablesToDefinitions;
import static de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.addReplacementVar;
import static de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getAndAddAuxVar;
import static de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getInVarIndex;
import static de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getInVarTerm;
import static de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getOutVarIndex;
import static de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getOutVarTerm;
import static de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination.MapEliminatorUtils.getReplacementVar;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import org.eclipse.swt.graphics.Pattern;
import java.util.Set;
import java.util.regex.*;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ContainsQuantifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.NonTheorySymbolFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.EqualityAnalysisResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IndexAnalyzer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author  Luca Bruder (luca.bruder@gmx.de)
 * @author  Lisa Kleinlein (lisa.kleinlein@web.de)
 */
public class MonniauxMapEliminator {
	

	public MonniauxMapEliminator( final IIcfg<?> icfg) {
		final IIcfg<?> micfg = icfg;
		final IcfgEdgeIterator iter = new IcfgEdgeIterator(micfg);
		
		while (iter.hasNext()) {
			final IIcfgTransition<?> transition = iter.next();
			final TransFormula tf = IcfgUtils.getTransformula(transition);
			int step = 0;
			
			
			/*String expr = "ABCD";
		    String test = "(sfksanohoa (select x y))";
		    for (String expr1 : test.split(" ")) {
		         expr = expr1;
		         expr = expr.substring(1);
		      	 break;
		         }*/
		    
		    String transformula = tf.toString();
		    String expr = null;
		    String x = null;
		    String y = null;
		    int index = 0;
			
			for (String expr1 : transformula.split(" (select * *)")) {
				
				for (int i = expr1.length() - 1; i >= 0; i--) {
					index = expr1.length();
					char c = expr1.charAt(i);
					if (c == '(') {
						expr = expr1.substring(i+1);
						i = 0;
						}
				}
				
				for (int i = index + 1; i < transformula.length(); i++) {
					char c = transformula.charAt(i);
					int index_left = 0;
					boolean left_found = false;
					boolean x_found = false;
					int index_right = 0;
					if (c == ' ') {
						index_left = i+1;
						left_found = true;
						}
					if (c == ' ' && left_found) {
						index_right = i-1;
						x = transformula.substring(index_left, index_right);
						x_found = true;
						}
					if (c == ')' && x_found) {
						y = transformula.substring(index_right + 1, i -1);
						i = transformula.length() + 1;
					}
					
				}
				
				
		
				String sub_transformula = "(and (=> (= y i_step) (= a_step_i x_i)) (expr a_step_i)";
				sub_transformula.replaceAll("y", y);
				sub_transformula.replaceAll("x", x);
				sub_transformula.replaceAll("expr", expr);
				sub_transformula.replaceAll("step", Integer.toString(step));
				
				//TermVariable t = new TermVariable("f_step", sort, null);
				
				Map <IProgramVar, TermVariable> inV = tf.getInVars();
				inV.remove(x);
				transformula = transformula.replaceAll("(* (select x y))", sub_transformula);
				Map <IProgramVar, TermVariable> outV = tf.getOutVars();
				outV.remove(x);
				//outV.merge(null, , null);
				step++;
				
			}
			
			/*
			for (true) {
			//todo	
			}
			
			TransFormula(inVars, outVars, auxVars, nonTheoryConst) newTF;
			*/
		}

	}

}
