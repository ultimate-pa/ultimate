/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCBaseTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Coercion;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;


public class CCInterpolator {
	
	Interpolator m_Interpolator;
	
	HashMap<SymmetricPair<CCTerm>, PathInfo> m_Paths;
	
	Theory m_Theory;
	int m_numInterpolants;
	
	Set<Term>[] m_Interpolants;

	/** 
	 * Compute the parent partition.  This is the next partition, whose
	 * subtree includes color.
	 */
	private int getParent(int color) {
		int parent = color + 1;
		while (m_Interpolator.m_startOfSubtrees[parent] > color)
			parent++;
		return parent;
	}
	
	/** 
	 * Compute the A-local child partition.  This is the child, that is
	 * A-local to the occurence.  This function returns -1 if all childs 
	 * are in B.
	 */
	private int getChild(int color, Occurrence occur) {
		/* find A-local child of m_Color */
		int child = color - 1;
		while (child >= m_Interpolator.m_startOfSubtrees[color]) {
			if (occur.isALocal(child))
				return child;
			child = m_Interpolator.m_startOfSubtrees[child] - 1;
		}
		return -1;
	}

	class PathInfo {
		CCTerm[] m_Path;
		CCEquality[] m_Lits;
		
		/**
		 * The set of partitions for which there is an AB-shared path
		 * from start to end.
		 */
		BitSet m_hasABPath;
		
		/**
		 * The first partition for which the path from start to end is 
		 * A-local.  This is m_numInterpolants, if there is no such 
		 * partition.  If m_hasABPath is not empty, this gives the
		 * first partition in this set.
		 */
		int m_MaxColor;
		PathEnd m_Head, m_Tail;

		/* max color is the maximum of all firstColor of all literals on the
		 * path.
		 * 
		 * Head color is the lastColor of the first literal before the first
		 * path change.  If head color >= max color, then there is no path
		 * change.
		 * 
		 */
		boolean m_Computed;

		class PathEnd {
			/**
			 * The first partition for which there is a A-local prefix of
			 * the path.  If m_hasABPath is non-empty, this is the first
			 * partition that is not in m_hasABPath, i.e. the first for which
			 * only a continuous A-path but not a continous B-path exists.  
			 */
			int         m_Color;
			/**
			 * For each partition on the path from m_Color to m_MaxColor this
			 * gives the term that ends the first A-local chain of equalities.
			 */
			Term[]      m_Term;
			/**
			 * For each partition on the path from m_Color to the root 
			 * (m_numInterpolants) this gives B-summaries that are used to
			 * gap congruence proofs, where both ends are A-local.
			 */
			Set<Term>[] m_Pre;
			
			@SuppressWarnings("unchecked")
			public PathEnd() {
				m_Color = m_numInterpolants;
				m_Term = new Term[m_numInterpolants];
				m_Pre = new Set[m_numInterpolants];
			}
			
			public void closeSingleAPath(PathEnd other, Term boundaryTerm, int color) {
				if (color < m_MaxColor) {
					addPre(color, Coercion.buildEq(boundaryTerm, m_Term[color]));
					addInterpolantClause(color, m_Pre[color]);
					m_Pre[color] = null;
					m_Term[color] = null;
				} else {
					assert (m_MaxColor == color);
					other.m_Term[color] = boundaryTerm;
					if (m_Pre[color] != null) {
						other.m_Pre[color] = m_Pre[color];
						m_Pre[color] = null;
					}
					m_MaxColor = getParent(color);
				}
			}

			/**
			 * 
			 */
			public void closeAPath(PathEnd other, Term boundaryTerm, Occurrence occur) {
				assert(m_hasABPath.isEmpty() || m_MaxColor == other.m_Color);
				assert(other.m_Color <= m_MaxColor);
				while (m_Color < m_numInterpolants && occur.isBLocal(m_Color)) {
					if (!m_hasABPath.get(m_Color))
						closeSingleAPath(other, boundaryTerm, m_Color);
					m_Color = getParent(m_Color);
				}
				m_hasABPath.and(occur.m_inA);
				if (!m_hasABPath.isEmpty()) {
					return;
				}
			}
			
			public void openAPath(PathEnd other, Term boundaryTerm, Occurrence occur) {
				while (true) {
					int child = getChild(m_Color, occur);
					/* if there is no A-local child, we are done. */
					if (child < 0)
						break;
					assert (occur.isALocal(child));
					if (m_hasABPath.get(child)) {
						m_MaxColor = other.m_Color = m_Color = child;
					} else {
						/* open a new A-path. */
						m_Term[child] = boundaryTerm;
						m_Color = child;
					}
				}
				m_hasABPath.and(occur.m_inB);
			}

			public Term getBoundTerm(int color) {
				if (color < m_Color) {
					CCTerm first = this == m_Head ? m_Path[0] 
							: m_Path[m_Path.length -1];
					return first.toSMTTerm(m_Theory);
				} else if (color < m_MaxColor) {
					return m_Term[color];
				} else {
					CCTerm last = this == m_Tail ? m_Path[0] 
							: m_Path[m_Path.length -1];
					return last.toSMTTerm(m_Theory);
				}
			}
			
			public void addPre(int color, Term pre) {
				if (m_Pre[color] == null)
					m_Pre[color] = new HashSet<Term>();
				m_Pre[color].add(pre);
			}
			
			public void addAllPre(int color, PathEnd src) {
				Set<Term> pre = src.m_Pre[color];
				if (pre == null)
					return;
				if (m_Pre[color] == null)
					m_Pre[color] = new HashSet<Term>();
				m_Pre[color].addAll(pre);
			}
			
			private void mergeCongPath(PathEnd other, CCAppTerm start, CCAppTerm end) {
				CCTerm term = start.getFunc();
				while (term instanceof CCAppTerm) {
					term = ((CCAppTerm) term).getFunc();
				}
				int rightColor = m_Interpolator
					.getOccurrence(end.getFlatTerm()).getALocalColor();
				Occurrence rightOccur = m_Interpolator.new Occurrence();
				rightOccur.occursIn(rightColor);
				Occurrence leftOccur = m_Interpolator.new Occurrence();
				leftOccur.occursIn(m_Color);
				FunctionSymbol func = ((CCBaseTerm)term).getFunctionSymbol();
				int numArgs = func.getParameterCount();
				PathInfo[] argPaths = new PathInfo[numArgs];
				PathEnd[] head = new PathEnd[numArgs];
				PathEnd[] tail = new PathEnd[numArgs];
				boolean[] isReverse = new boolean[numArgs];
				int arg = numArgs;
				while (true) {
					arg--;
					argPaths[arg] =  
						start.getArg() == end.getArg() ? new PathInfo(start.getArg())
					  : m_Paths.get(new SymmetricPair<CCTerm>(start.getArg(), end.getArg()));
					argPaths[arg].interpolatePathInfo();
					isReverse[arg] = !(start.getArg() == argPaths[arg].m_Path[0]);
					head[arg] = isReverse[arg] ? argPaths[arg].m_Tail : argPaths[arg].m_Head;
					tail[arg] = isReverse[arg] ? argPaths[arg].m_Head : argPaths[arg].m_Tail;
					Term startTerm = start.getArg().toSMTTerm(m_Theory);
					head[arg].closeAPath(tail[arg], startTerm, leftOccur);
					head[arg].openAPath(tail[arg], startTerm, leftOccur);
					Term endTerm = end.getArg().toSMTTerm(m_Theory);
					tail[arg].closeAPath(head[arg], endTerm, rightOccur);
					tail[arg].openAPath(head[arg], endTerm, rightOccur);
					if (arg == 0)
						break;
					
					start = (CCAppTerm) start.getFunc();
					end = (CCAppTerm) end.getFunc();
				}
				
				while (rightOccur.isBLocal(m_Color)) {
					Term[] boundaryParams = new Term[numArgs];
					for (int i = 0; i < numArgs; i++) {
						boundaryParams[i] = head[i].getBoundTerm(m_Color);
						addAllPre(m_Color, tail[i]);
					}
					Term boundaryTerm = Coercion.buildApp(func, boundaryParams);
					closeSingleAPath(other, boundaryTerm, m_Color);
					m_Color = getParent(m_Color);
				}
				int highColor = m_Color;
				while (true) {
					/* find A-local child of m_Color */
					int child = getChild(m_Color, rightOccur);
					if (child < 0)
						break;
					m_Color = child;
					Term[] boundaryParams = new Term[numArgs];
					for (int i = 0; i < numArgs; i++) {
						boundaryParams[i] = tail[i].getBoundTerm(m_Color);
						addAllPre(m_Color, tail[i]);
					}
					Term boundaryTerm = Coercion.buildApp(func, boundaryParams);
					m_Term[m_Color] = boundaryTerm;
				}
				assert (m_Color == rightColor);
				for (int color = highColor; 
						color < m_numInterpolants; color = getParent(color)) {
					for (int i = 0; i < numArgs; i++) {
						if (color < argPaths[i].m_MaxColor)
							addPre(color, Coercion.buildDistinct(
									head[i].getBoundTerm(color),
									tail[i].getBoundTerm(color)));
						addAllPre(color, head[i]);
						addAllPre(color, tail[i]);
					}
				}
			}
			
			public String toString() {
				StringBuilder sb = new StringBuilder();
				String comma = "";
				sb.append(m_Color).append(":[");
				for (int i = m_Color; i < m_MaxColor; i++) {
					sb.append(comma);
					if (m_Pre[i] != null)
						sb.append(m_Pre[i]).append(" or ");
					sb.append(m_Term[i]);
					comma = ",";
				}
				comma = "|";
				for (int i = m_MaxColor; i < m_numInterpolants; i++) {
					if (m_Pre[i] != null) {
						sb.append(comma).append("pre").append(i).append(":");
						sb.append(m_Pre[i]);
						comma = ",";
					}
				}
				sb.append("]");
				return sb.toString();
			}
		}		
		
		/* invariants:
		 *  HeadTerm[p] != null exactly for p in [m_HeadColor, m_MaxColor-1]
		 *  HeadPre[p] != null only for p in [m_HeadColor, numInterpolants]
		 *  HeadColor is in between first and last color of head term.
		 *  likewise for Tail.
		 *  MaxColor is maximum of all first of all terms and literals
		 *  involved in current path (but there may be bigger literals in
		 *  congruence paths that were added to headPre/tailPre).
		 *  
		 *  The partial interpolant of the current path is 
		 *    m_Interpolants &&
		 *       HeadPre ==> Lits[0] == m_HeadTerm && 
		 *       TailPre ==> m_TailTerm == lits[n]
		 *  where HeadTerm = Lits[0] for partitions < HeadColor and
		 *        TailTerm = Lits[n] for partitions < TailColor.
		 *
		 *  For partitions >= maxColor, everything so far was in A, so
		 *  the partial interpolant of the current path is 
		 *    m_Interpolants &&
		 *       TailPre ==> Lits[0] == lits[n]
		 */
		
		public PathInfo(CCTerm[] path, CCEquality[] litsOnPath) {
			m_Path = path;
			m_Lits = litsOnPath;
			m_hasABPath = new BitSet(m_numInterpolants);
			m_hasABPath.set(0, m_numInterpolants);
			m_MaxColor = m_numInterpolants;
		}
		
		public PathInfo(CCTerm arg) {
			this(new CCTerm[] { arg }, new CCEquality[0]);
		}

		public void interpolatePathInfo() {
			if (m_Computed)
				return;
			Occurrence headOccur = 
					m_Interpolator.getOccurrence(m_Path[0].getFlatTerm());
			m_Head = new PathEnd();
			m_Tail = new PathEnd();
			m_Tail.closeAPath(m_Head, null, headOccur);
			m_Tail.openAPath(m_Head, null, headOccur);
			
			for (int i = 0; i < m_Lits.length; i++) {
				if (m_Lits[i] == null) {
					CCAppTerm left = (CCAppTerm) m_Path[i];
					CCAppTerm right = (CCAppTerm) m_Path[i+1];
					m_Tail.mergeCongPath(m_Head, left, right);
				} else {
					LitInfo info = m_Interpolator.getLiteralInfo(m_Lits[i]);
					Term boundaryTerm;
					boundaryTerm = m_Path[i].toSMTTerm(m_Theory);
					if (info.getMixedVar() != null) {
						m_Tail.closeAPath(m_Head, boundaryTerm, info);
						m_Tail.openAPath(m_Head, boundaryTerm, info);
						Occurrence occ = m_Interpolator.getOccurrence(m_Path[i+1].getFlatTerm());
						boundaryTerm = info.getMixedVar();
						m_Tail.closeAPath(m_Head, boundaryTerm, occ);
						m_Tail.openAPath(m_Head, boundaryTerm, occ);
					} else {
						m_Tail.closeAPath(m_Head, boundaryTerm, info);
						m_Tail.openAPath(m_Head, boundaryTerm, info);
					}
				}
			}
			m_Computed= true;
		}

		/**
		 * Build an interpolant clause and add it to the interpolant set.
		 * @param pre  The disequalities summarizing the requirements from
		 *             the B-part in skipped argument paths.
		 * @param lhsTerm The end of the A-equality chain. 
		 * @param rhsTerm The start of the A-equality chain.
		 * @param isNegated True, if there is a disequality in the chain.
		 */
		private void addInterpolantClause(int color, Set<Term> pre) {
			Term clause = pre == null ? m_Theory.FALSE
						: m_Theory.or(pre.toArray(new Term[pre.size()]));
			m_Interpolants[color].add(clause);
		}

		public String toString() {
			return "PathInfo["+Arrays.toString(m_Path)+","
					+ m_Head + ',' + m_Tail + "," + m_MaxColor+"]";
		}

		public void addDiseq(CCEquality diseq) {
			LitInfo info = m_Interpolator.getLiteralInfo(diseq);
			Term boundaryTailTerm, boundaryHeadTerm;
			boundaryHeadTerm = m_Path[0].toSMTTerm(m_Theory);
			boundaryTailTerm = m_Path[m_Path.length - 1].toSMTTerm(m_Theory);
			if (info.getMixedVar() != null) {
				Occurrence occHead = m_Interpolator.getOccurrence(m_Path[0].getFlatTerm());
				m_Head.closeAPath(m_Tail, boundaryHeadTerm, info);
				m_Head.openAPath(m_Tail, boundaryHeadTerm, info);
				Occurrence occTail = m_Interpolator.getOccurrence(m_Path[m_Path.length - 1].getFlatTerm());
				m_Tail.closeAPath(m_Head, boundaryTailTerm, info);
				m_Tail.openAPath(m_Head, boundaryTailTerm, info);

				m_Head.closeAPath(m_Tail, info.getMixedVar(), occTail);
				m_Tail.closeAPath(m_Head, info.getMixedVar(), occHead);
			} else {
				m_Tail.closeAPath(m_Head, boundaryTailTerm, info);
				m_Tail.openAPath(m_Head, boundaryTailTerm, info);
				m_Head.closeAPath(m_Tail, boundaryHeadTerm, info);
				m_Head.openAPath(m_Tail, boundaryHeadTerm, info);
			}
		}

		private void reversePath() {
			PathEnd temp = m_Head;
			m_Head = m_Tail;
			m_Tail = temp;
		}

		public void close() {
			while (m_Head.m_Color < m_numInterpolants ||
					m_Tail.m_Color < m_numInterpolants) {
				if (m_Head.m_Color < m_Tail.m_Color) {
					m_Head.addPre(m_Head.m_Color, Coercion.buildEq
							(m_Head.getBoundTerm(m_Head.m_Color), m_Tail.getBoundTerm(m_MaxColor)));
					addInterpolantClause(m_Head.m_Color, m_Head.m_Pre[m_Head.m_Color]);
					int parent = m_Head.m_Color + 1;
					while (m_Interpolator.m_startOfSubtrees[parent] > m_Head.m_Color)
						parent++;
					m_Head.m_Color = parent;
				} else if (m_Head.m_Color == m_Tail.m_Color) {
					m_Head.addAllPre(m_Head.m_Color, m_Tail);
					m_Tail.m_Pre[m_Tail.m_Color] = null;
					if (m_Head.m_Color < m_MaxColor) {
						m_Head.addPre(m_Head.m_Color, Coercion.buildDistinct
								(m_Head.getBoundTerm(m_Head.m_Color), m_Tail.getBoundTerm(m_Head.m_Color)));
					}
					addInterpolantClause(m_Head.m_Color, m_Head.m_Pre[m_Head.m_Color]);
					int parent = m_Head.m_Color + 1;
					while (m_Interpolator.m_startOfSubtrees[parent] > m_Head.m_Color)
						parent++;
					m_Head.m_Color = parent;
					m_Tail.m_Color = parent;
				} else {
					m_Tail.addPre(m_Tail.m_Color, Coercion.buildEq
							(m_Head.getBoundTerm(m_MaxColor), m_Tail.getBoundTerm(m_Tail.m_Color)));
					addInterpolantClause(m_Tail.m_Color, m_Tail.m_Pre[m_Tail.m_Color]);
					int parent = m_Tail.m_Color + 1;
					while (m_Interpolator.m_startOfSubtrees[parent] > m_Tail.m_Color)
						parent++;
					m_Tail.m_Color = parent;
				}
			}
		}
	}
	
	@SuppressWarnings("unchecked")
	public CCInterpolator(Interpolator ipolator) {
		m_Interpolator = ipolator;
		m_numInterpolants = ipolator.m_NumInterpolants;
		m_Theory = ipolator.m_Theory;
		m_Paths = new HashMap<SymmetricPair<CCTerm>, PathInfo>();
		m_Interpolants = new Set[m_numInterpolants];
		for (int i = 0; i < m_numInterpolants; i++)
			m_Interpolants[i] = new HashSet<Term>();
	}
	
	public Term[] computeInterpolants(CCAnnotation annot) {
		PathInfo mainPath = null; 
		CCTerm[][] paths = annot.getPaths();
		CCEquality[][] lits = annot.getLitsOnPaths();
		for (int i = 0; i < paths.length; i++) {
			CCTerm first = paths[i][0];
			CCTerm last = paths[i][paths[i].length-1];
			PathInfo pathInfo = new PathInfo(paths[i], lits[i]);
			m_Paths.put(new SymmetricPair<CCTerm>(first, last), 
					pathInfo);
			if (i == 0)
				mainPath = pathInfo;
		}
		mainPath.interpolatePathInfo();
		CCEquality diseq = annot.getDiseq();
		if (diseq != null)
			mainPath.addDiseq(diseq);
		mainPath.close();
		Term[] interpolants = new Term[m_numInterpolants];
		for (int i = 0; i < m_numInterpolants; i++) {
			interpolants[i] = m_Theory.and
				(m_Interpolants[i].toArray(new Term[m_Interpolants[i].size()]));
		}
		return interpolants;
	}
	
	public String toString() {
		return Arrays.toString(m_Interpolants); 
	}
}
