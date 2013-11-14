package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.List;

public class BinSearch<E> {

	public static interface Driver<E> {
		public void prepare(List<E> sublist);
		public void failure(List<E> sublist);
		public void success(List<E> sublist);
	}
	
	private static class IntPair {
		int first;
		int second;
		public IntPair(int f, int s) {
			first = f;
			second = s;
		}
	}
	
	private List<E> m_List;
	private Driver<E> m_Driver;
	private ArrayDeque<IntPair> m_Todo;
	
	public BinSearch(List<E> list, Driver<E> driver) {
		m_List = list;
		m_Driver = driver;
		m_Todo = new ArrayDeque<IntPair>();
	}
	
	public boolean run(Minimizer tester) throws IOException, InterruptedException {
		if (m_List.isEmpty())
			return false;
		boolean result = false;
		m_Todo.push(new IntPair(0, m_List.size()));
		while (!m_Todo.isEmpty()) {
			IntPair p = m_Todo.pop();
			List<E> sublist = m_List.subList(p.first, p.second);
			if (sublist.isEmpty())
				continue;
			m_Driver.prepare(sublist);
			if (tester.test()) {
				m_Driver.success(sublist);
				result = true;
			} else {
				m_Driver.failure(sublist);
				// Split into two new sublists
				int mid = (p.first + p.second) / 2;
				if (mid == p.first)
					continue;
				if (mid < p.second)
					m_Todo.push(new IntPair(mid, p.second));
				if (p.first < mid);
					m_Todo.push(new IntPair(p.first, mid));
			}
		}
		return result;
	}

}
