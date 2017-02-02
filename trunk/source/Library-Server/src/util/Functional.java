package util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;

public interface Functional {
	public interface Exceptional<E extends Throwable, F> {
		default RuntimeException wrap(E e) {
			return new RuntimeException(e);
		}

		F silence(Class<E> CE);
	}

	@FunctionalInterface
	public interface EConsumer<T, E extends Throwable> extends Exceptional<E, Consumer<T>> {
		void consume(T t) throws E;

		default Consumer<T> silence(Class<E> CE) {
			return t -> {
				try {
					consume(t);
				} catch (Throwable e) {
					if (CE.isInstance(e)) {

					} else {
						//throw e;
					}
				}
			};
		}
	}

	static <T1, U> BiFunction<T1, U, T1> chainWrap(BiConsumer<T1, U> bc) {
		return (t1, u) -> {
			try {
				bc.accept(t1, u);
			} catch (Exception e) {

			}
			return t1;
		};
	}

}
