package de.uni_freiburg.informatik.ultimate.interactive;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * Interface that provides a way to convert between Types.
 * 
 * @author Julian Jarecki
 *
 * @param <A,B>
 */
public interface IConverterRegistry<IA, IB> {
	<A extends IA> IConverter<A, ? extends IB> getAB(final Class<A> typeA);

	<B extends IB> IConverter<? extends IA, B> getAB2(final Class<B> typeB);

	<B extends IB> IConverter<B, ? extends IA> getBA(final Class<B> typeB);

	<A extends IA> IConverter<? extends IB, A> getBA2(final Class<A> typeA);

	<A extends IA, B extends IB> void registerAB(IConverter<A, B> converter);

	<A extends IA, B extends IB> void registerBA(IConverter<B, A> converter);

	default <A extends IA, B extends IB> void registerAB(Class<A> tA, Class<B> tB, Function<A, B> a2b) {
		registerAB(converter(tA, tB, a2b));
	}

	default <A extends IA, B extends IB> void registerBA(Class<A> tA, Class<B> tB, Function<B, A> b2a) {
		registerBA(converter(tB, tA, b2a));
	}

	static <A, B> IConverter<A, B> converter(Class<A> tA, Class<B> tB, Function<A, B> a2b) {
		return new IConverter<A, B>() {

			@Override
			public Class<A> getTypeA() {
				return tA;
			}

			@Override
			public Class<B> getTypeB() {
				return tB;
			}

			@Override
			public B apply(A a) {
				return a2b.apply(a);
			}
		};
	}

	public static interface IConverter<A, B> extends Function<A, B> {
		Class<A> getTypeA();

		Class<B> getTypeB();

		default Consumer<A> andThen(Consumer<B> consumer) {
			return a -> consumer.accept(apply(a));
		}
		
		default Consumer<A> test() {
			return a -> {};
		}

		default Supplier<B> compose(Supplier<A> supplier) {
			return () -> apply(supplier.get());
		}
	}

	public static interface IBiConverter<A, B> extends IConverter<A, B> {
		IConverter<B, A> inverse();
	}

	static <A, B> IBiConverter<A, B> combine(IBiConverter<A, B> forth, IBiConverter<B, A> back) {
		return new IBiConverter<A, B>() {

			@Override
			public Class<A> getTypeA() {
				return forth.getTypeA();
			}

			@Override
			public Class<B> getTypeB() {
				return forth.getTypeB();
			}

			@Override
			public B apply(A a) {
				return forth.apply(a);
			}

			@Override
			public IConverter<B, A> inverse() {
				return back;
			}
		};
	}
}
