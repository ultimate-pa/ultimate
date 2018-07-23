/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE MSO Library package.
 *
 * The ULTIMATE MSO Library package library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE MSO Library package library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE MSO Library package. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE MSO Library package, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE MSO Library package library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.mso;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class MoNatDiffScript implements Script {
	
	private final ILogger mLogger;

	public MoNatDiffScript(ILogger logger) {
		mLogger = logger;
	}

	@Override
	public void setLogic(String logic) throws UnsupportedOperationException, SMTLIBException {
		mLogger.info("hello world, logic set to " + logic);
	}

	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mLogger.info("hello world, logic set to " + logic);
	}

	@Override
	public void setOption(String opt, Object value) throws UnsupportedOperationException, SMTLIBException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void setInfo(String info, Object value) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition) throws SMTLIBException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort) throws SMTLIBException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort, Term definition) throws SMTLIBException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void push(int levels) throws SMTLIBException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void pop(int levels) throws SMTLIBException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public LBool checkSatAssuming(Term... assumptions) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term[] getUnsatAssumptions() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object getOption(String opt) throws UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Object getInfo(String info) throws UnsupportedOperationException, SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void exit() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public Sort sort(String sortname, Sort... params) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Sort sort(String sortname, BigInteger[] indices, Sort... params) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Sort[] sortVariables(String... names) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term term(String funcname, Term... params) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term term(String funcname, BigInteger[] indices, Sort returnSort, Term... params) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public TermVariable variable(String varname, Sort sort) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term quantifier(int quantor, TermVariable[] vars, Term body, Term[]... patterns) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term let(TermVariable[] vars, Term[] values, Term body) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term annotate(Term t, Annotation... annotations) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term numeral(String num) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term numeral(BigInteger num) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term decimal(String decimal) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term decimal(BigDecimal decimal) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term hexadecimal(String hex) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term binary(String bin) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term string(String str) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term simplify(Term term) throws SMTLIBException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void resetAssertions() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public Term[] getInterpolants(Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<Term[]> checkAllsat(Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Term[] findImpliedEquality(Term[] x, Term[] y) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public QuotedObject echo(QuotedObject msg) {
		// TODO Auto-generated method stub
		return null;
	}

}
