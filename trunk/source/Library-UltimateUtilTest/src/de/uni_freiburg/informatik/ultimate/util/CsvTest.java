package de.uni_freiburg.informatik.ultimate.util;

import java.util.Arrays;
import java.util.Map;
import java.util.Map.Entry;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvUtils.IExplicitConverter;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

public class CsvTest {

	@Test
	public void testCsvConvert() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(new String[] { "Title" });
		SimpleCsvProvider<Long> B = new SimpleCsvProvider<>(new String[] { "Title" });

		A.addRow("Row", new Integer[] { 1 });
		B.addRow("Row", new Long[] { 1L });

		ICsvProvider<Long> something = CsvUtils.convert(A, new IExplicitConverter<Integer, Long>() {
			@Override
			public Long convert(Integer something) {
				return something.longValue();
			}

			@Override
			public Long[] createArray(int length) {
				return new Long[length];
			}

		});
		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvFlatten() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(new String[] { "A", "B", "C" });
		A.addRow("Row 1", new Integer[] { 1, 2, 3 });
		A.addRow("Row 2", new Integer[] { 4, 5, 6 });

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(new String[] { "A-Row 1", "A-Row 2", "B-Row 1",
				"B-Row 2", "C-Row 1", "C-Row 2" });
		B.addRow("", new Integer[] { 1, 4, 2, 5, 3, 6 });

		ICsvProvider<Integer> something = CsvUtils.flatten(A, "-", new Integer[0]);

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvProject() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(new String[] { "A", "B", "C" });
		A.addRow("Row 1", new Integer[] { 1, 2, 3 });
		A.addRow("Row 2", new Integer[] { 4, 5, 6 });

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(new String[] { "A" });
		B.addRow("Row 1", new Integer[] { 1 });
		B.addRow("Row 2", new Integer[] { 4 });

		ICsvProvider<Integer> something = CsvUtils.projectColumn(A, "A");

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvProjectEmpty() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(new String[] { "A", "B", "C" });

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(new String[] { "A" });

		ICsvProvider<Integer> something = CsvUtils.projectColumn(A, "A");

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvProjectCollection() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(new String[] { "A", "B", "C" });
		A.addRow("Row 1", new Integer[] { 1, 2, 3 });
		A.addRow("Row 2", new Integer[] { 4, 5, 6 });

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(new String[] { "A", "B" });
		B.addRow("Row 1", new Integer[] { 1, 2 });
		B.addRow("Row 2", new Integer[] { 4, 5 });

		ICsvProvider<Integer> something = CsvUtils.projectColumn(A, Arrays.asList(new String[] { "A", "B" }));

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvConcatenate() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(new String[] { "A", "B", "C" });
		A.addRow("Row 1", new Integer[] { 1, 2, 3 });
		A.addRow("Row 2", new Integer[] { 4, 5, 6 });

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(new String[] { "A", "B", "C" });
		B.addRow("Row 3", new Integer[] { 1, 2, 3 });
		B.addRow("Row 4", new Integer[] { 4, 5, 6 });

		SimpleCsvProvider<Integer> C = new SimpleCsvProvider<>(new String[] { "A", "B", "C" });
		C.addRow("Row 1", new Integer[] { 1, 2, 3 });
		C.addRow("Row 2", new Integer[] { 4, 5, 6 });
		C.addRow("Row 3", new Integer[] { 1, 2, 3 });
		C.addRow("Row 4", new Integer[] { 4, 5, 6 });

		ICsvProvider<Integer> something = CsvUtils.concatenateRows(A, B);

		Assert.assertTrue("something is not equal to B", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}

	@Test
	public void testCsvAddColumn() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(new String[] { "A", "B", "C" });
		A.addRow("Row 1", new Integer[] { 1, 2, 3 });
		A.addRow("Row 2", new Integer[] { 4, 5, 6 });

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(new String[] { "A", "B" });
		B.addRow("Row 1", new Integer[] { 1, 2 });
		B.addRow("Row 2", new Integer[] { 4, 5 });

		ICsvProvider<Integer> something = CsvUtils.addColumn(B, "C", 2, new Integer[] { 3, 6 });

		Assert.assertTrue("something is not equal to A", contentAsStringIsEqual(A.getTable(), something.getTable()));
	}
	
	@Test
	public void testCsvTranspose() {
		SimpleCsvProvider<Integer> A = new SimpleCsvProvider<>(new String[] { "A", "B", "C" });
		A.addRow("Row 1", new Integer[] { 1, 2, 3 });
		A.addRow("Row 2", new Integer[] { 4, 5, 6 });

		SimpleCsvProvider<Integer> B = new SimpleCsvProvider<>(new String[] { "Row 1", "Row 2" });
		B.addRow("A", new Integer[] { 1, 4 });
		B.addRow("B", new Integer[] { 2, 5 });
		B.addRow("C", new Integer[] { 3, 6 });

		ICsvProvider<Integer> something = CsvUtils.transpose(A);

		Assert.assertTrue("something is not equal to A", contentAsStringIsEqual(B.getTable(), something.getTable()));
	}
	
	private <T> boolean contentAsStringIsEqual(Map<String, T[]> mapA, Map<String, T[]> mapB) {
		for (Entry<String, T[]> entry : mapA.entrySet()) {
			T[] entryB = mapB.get(entry.getKey());

			if (entryB.length != entry.getValue().length) {
				return false;
			}

			for (int i = 0; i < entryB.length; ++i) {
				if (!entryB[i].equals(entry.getValue()[i])) {
					return false;
				}
			}
		}
		return true;
	}

}
