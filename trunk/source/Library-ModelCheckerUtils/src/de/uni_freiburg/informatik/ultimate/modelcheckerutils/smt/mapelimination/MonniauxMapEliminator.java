/*
 * Copyright (C) 2018 Luca Bruder (luca.bruder@gmx.de)
 * Copyright (C) 2018 Lisa Kleinlein (lisa.kleinlein@web.de)
 *
 * This file is part of the ULTIMATE Library-ModelCheckerUtils library.
 *
 * The ULTIMATE Library-ModelCheckerUtils library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Library-ModelCheckerUtils library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-ModelCheckerUtils library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-ModelCheckerUtils library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-ModelCheckerUtils library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * @author Luca Bruder (luca.bruder@gmx.de)
 * @author Lisa Kleinlein (lisa.kleinlein@web.de)
 */
public class MonniauxMapEliminator {

	public MonniauxMapEliminator(final IIcfg<?> icfg) {
		final IIcfg<?> micfg = icfg;
		final IcfgEdgeIterator iter = new IcfgEdgeIterator(micfg);

		while (iter.hasNext()) {
			final IIcfgTransition<?> transition = iter.next();
			final TransFormula tf = IcfgUtils.getTransformula(transition);
			int step = 0;

			/*
			 * String expr = "ABCD"; String test = "(sfksanohoa (select x y))"; for (String expr1 : test.split(" ")) {
			 * expr = expr1; expr = expr.substring(1); break; }
			 */

			String transformula = tf.toString();
			String expr = null;
			String x = null;
			String y = null;
			int index = 0;

			for (final String expr1 : transformula.split(" (select * *)")) {

				for (int i = expr1.length() - 1; i >= 0; i--) {
					index = expr1.length();
					final char c = expr1.charAt(i);
					if (c == '(') {
						expr = expr1.substring(i + 1);
						i = 0;
					}
				}

				for (int i = index + 1; i < transformula.length(); i++) {
					final char c = transformula.charAt(i);
					int index_left = 0;
					boolean left_found = false;
					boolean x_found = false;
					int index_right = 0;
					if (c == ' ') {
						index_left = i + 1;
						left_found = true;
					}
					if (c == ' ' && left_found) {
						index_right = i - 1;
						x = transformula.substring(index_left, index_right);
						x_found = true;
					}
					if (c == ')' && x_found) {
						y = transformula.substring(index_right + 1, i - 1);
						i = transformula.length() + 1;
					}

				}

				final String sub_transformula = "(and (=> (= y i_step) (= a_step_i x_i)) (expr a_step_i)";
				sub_transformula.replaceAll("y", y);
				sub_transformula.replaceAll("x", x);
				sub_transformula.replaceAll("expr", expr);
				sub_transformula.replaceAll("step", Integer.toString(step));

				// TermVariable t = new TermVariable("f_step", sort, null);

				final Map<IProgramVar, TermVariable> inV = tf.getInVars();
				inV.remove(x);
				transformula = transformula.replaceAll("(* (select x y))", sub_transformula);
				final Map<IProgramVar, TermVariable> outV = tf.getOutVars();
				outV.remove(x);
				// outV.merge(null, , null);
				step++;

			}

			/*
			 * for (true) { //todo }
			 *
			 * TransFormula(inVars, outVars, auxVars, nonTheoryConst) newTF;
			 */
		}

	}

}
