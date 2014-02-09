package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.List;
import java.util.TreeMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.result.ResultUtil;

public class ModuleDecompositionBenchmark {
	
	private class RankingFunction {
		private final String m_Name;
		private final Expression[] m_LexExpressions;
		public RankingFunction(String name, Expression[] lexExpressions) {
			super();
			m_Name = name;
			m_LexExpressions = lexExpressions;
		}
//		public String getName() {
//			return m_Name;
//		}
//		public Expression[] getLexExpressions() {
//			return m_LexExpressions;
//		}
		@Override
		public String toString() {
			List<ITranslator<?, ?, ?, ?>> translatorSequence = 
					UltimateServices.getInstance().getTranslatorSequence();
			return m_Name + " " + ResultUtil.backtranslationWorkaround(
					translatorSequence,m_LexExpressions);
		}
		
	}

	private final TreeMap<Integer,Integer> m_ModuleSizeTrivial = new TreeMap<Integer,Integer>();
	private final TreeMap<Integer,Integer> m_ModuleSizeDeterministic = new TreeMap<Integer,Integer>();
	private final TreeMap<Integer,Integer> m_ModuleSizeNondeterministic = new TreeMap<Integer,Integer>();
	private final TreeMap<Integer,RankingFunction> m_RankingFunction = new TreeMap<Integer,RankingFunction>();
	
	
	void reportTrivialModule(Integer iteration, Integer size) {
		m_ModuleSizeTrivial.put(iteration, size);
	}
	
	void reportDeterminsticModule(Integer iteration, Integer size) {
		m_ModuleSizeDeterministic.put(iteration, size);
	}
	
	void reportNonDeterminsticModule(Integer iteration, Integer size) {
		m_ModuleSizeNondeterministic.put(iteration, size);
	}
	
	void reportRankingFunction(Integer iteration, String rfName, Expression[] asLexExpression) {
		m_RankingFunction.put(iteration, new RankingFunction(rfName, asLexExpression));
	}
	
	@Override
	public String toString() {
//		TreeMap<Integer, Integer> ms = bcl.getModuleSize();
		int modules = m_ModuleSizeTrivial.size() + m_ModuleSizeDeterministic.size() + m_ModuleSizeNondeterministic.size();
		if (modules == 0) {
			return "Trivially terminating. There is no loop in your program.";
		}
		int modulesWithTrivialRankingFunction = 0;
		int maxNumberOfStatesOfModuleWithTrivialRankingFunction = 0;
		StringBuilder sb = new StringBuilder();
		sb.append("Your program was decomposed into ");
		sb.append(modules);
		sb.append(" modules. ");
		sb.append("(");
		sb.append(m_ModuleSizeTrivial.size());
		sb.append(" trivial, ");
		sb.append(m_ModuleSizeDeterministic.size());
		sb.append(" deterministic, ");
		sb.append(m_ModuleSizeNondeterministic.size());
		sb.append(" nondeterministic) ");
		for (Entry<Integer, Integer> entry  : m_ModuleSizeDeterministic.entrySet()) {
			if (m_RankingFunction.containsKey(entry.getKey())) {
				sb.append("One deterministic module has ");
				sb.append(m_RankingFunction.get(entry.getKey()).toString());
				sb.append(" and consists of ");
				sb.append(entry.getValue());
				sb.append(" locations. ");
			} else {
				modulesWithTrivialRankingFunction++;
				if (entry.getValue() > maxNumberOfStatesOfModuleWithTrivialRankingFunction) {
					maxNumberOfStatesOfModuleWithTrivialRankingFunction = entry.getValue();
				}
			}
		}
		for (Entry<Integer, Integer> entry : m_ModuleSizeNondeterministic.entrySet()) {
			if (m_RankingFunction.containsKey(entry.getKey())) {
				sb.append("One nondeterministic module has ");
				sb.append(m_RankingFunction.get(entry.getKey()).toString());
				sb.append(" and consists of ");
				sb.append(entry.getValue());
				sb.append(" locations. ");
			} else {
				modulesWithTrivialRankingFunction++;
				if (entry.getValue() > maxNumberOfStatesOfModuleWithTrivialRankingFunction) {
					maxNumberOfStatesOfModuleWithTrivialRankingFunction = entry.getValue();
				}
			}
		}
		if (modulesWithTrivialRankingFunction > 0) {
			sb.append(modulesWithTrivialRankingFunction);
			sb.append(" modules have a trivial ranking function, the largest among these consists of ");
			sb.append(maxNumberOfStatesOfModuleWithTrivialRankingFunction);
			sb.append(" locations.");
		}
		return sb.toString();
	}


}
