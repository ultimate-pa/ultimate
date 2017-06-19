package de.uni_freiburg.informatik.ultimate.interactive.conversion;

import java.util.Objects;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionStage;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractiveQueue;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.IConverterRegistry.IConverter;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.IConverterRegistry.IResponseConverter;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.UnregisteredTypeException;
import de.uni_freiburg.informatik.ultimate.interactive.utils.InheritanceUtil;

public class ApplyConversionToInteractive<M, O> implements IInteractive<M> {
	private final IInteractive<O> mOriginal;
	private final IConverterRegistry<O, M> mConverter;
	private final Class<M> mTypeBound;

	public ApplyConversionToInteractive(final IInteractive<O> original, final IConverterRegistry<O, M> converter,
			final Class<M> typeBound) {
		mOriginal = original;
		mConverter = converter;
		mTypeBound = typeBound;
	}

	@Override
	public <T extends M> void register(final Class<T> type, final Consumer<T> consumer) {
		final IConverter<? extends O, T> converter = mConverter.getAB2(type);
		wrapRegister(converter, mOriginal, consumer);
	}

	private static <M, T> void wrapRegister(final IConverter<M, T> src, final IInteractive<? super M> old,
			final Consumer<T> consumer) {
		old.register(src.getTypeA(), src.andThen(consumer));
	}

	@Override
	public <T extends M> void register(final Class<T> type, final Supplier<T> supplier) {
		final IConverter<T, ? extends O> converter = mConverter.getBA(type);
		wrapRegister(converter, mOriginal, supplier);
	}

	private static <M, T> void wrapRegister(final IConverter<T, M> src, final IInteractive<? super M> old,
			final Supplier<T> supplier) {
		old.register(src.getTypeB(), src.compose(supplier));
	}

	@Override
	public <T extends M, D extends M> void register(final Class<T> type, final Class<D> dataType,
			final Function<D, T> supplier) {
		final IConverter<T, ? extends O> converter = mConverter.getBA(type);
		final IConverter<? extends O, D> dConverter = mConverter.getAB2(dataType);
		wrapRegister(type, converter, dConverter, supplier);
	}

	private <D extends M, T extends M, O1 extends O, O2 extends O> void wrapRegister(final Class<T> type,
			final IConverter<T, O1> converter, final IConverter<O2, D> dConverter, final Function<D, T> supplier) {
		final Function<O2, O1> cSupplier = d -> converter.apply(supplier.apply(dConverter.apply(d)));
		mOriginal.register(converter.getTypeB(), dConverter.getTypeA(), cSupplier);
	}

	@Override
	public void send(final M data) {
		@SuppressWarnings("unchecked")
		final Class<? extends M> type = (Class<? extends M>) data.getClass();
		IConverter<? extends M, ? extends O> converter;
		converter = mConverter.getBA(type);
		if (converter == null) {
			final Function<Class<? extends M>, IConverter<? extends M, ? extends O>> mapper = mConverter::getBA;
			converter = InheritanceUtil.getInheritance(type, mTypeBound).stream().map(mapper).filter(Objects::nonNull)
					.findFirst().orElseThrow(() -> new UnregisteredTypeException(type));
		}
		wrapSend(converter, data);
	}

	@SuppressWarnings("unchecked")
	private <M1 extends M, T extends O> void wrapSend(final IConverter<M1, T> src, final M data) {
		mOriginal.send(src.apply((M1) data));
	}

	@Override
	public <T extends M> CompletableFuture<T> request(final Class<T> type) {
		final IConverter<? extends O, T> converter = mConverter.getAB2(type);
		if (converter==null) throw new UnregisteredTypeException(type);
		return wrapRequest(converter);
	}

	private <O1 extends O, T extends M> CompletableFuture<T> wrapRequest(final IConverter<O1, T> converter) {
		return mOriginal.request(converter.getTypeA()).thenApply(converter);
	}

	@Override
	public <T extends M> CompletableFuture<T> request(final Class<T> type, final M data) {
		@SuppressWarnings("unchecked")
		final Class<? extends M> dType = (Class<? extends M>) data.getClass();
		final IConverter<? extends M, ? extends O> dConverter = mConverter.getBA(dType);
		if (dConverter == null)
			throw new UnregisteredTypeException(dType);
		return wrapPreRequest(dConverter, data, type);
	}

	private <T extends M, D extends M, OD extends O> CompletableFuture<T>
			wrapPreRequest(final IConverter<D, OD> dConverter, final M data, final Class<T> type) {
		final Class<D> dType = dConverter.getTypeA();
		@SuppressWarnings("unchecked")
		final D dData = (D) data;
		final OD oData = dConverter.apply(dData);

		final IResponseConverter<? extends O, D, T> rConverter = mConverter.getRConv(type, dType);
		if (rConverter != null) {
			return wrapRRequest(rConverter, dData, oData);
		}

		final IConverter<? extends O, T> converter = mConverter.getAB2(type);
		if (converter==null) throw new UnregisteredTypeException(type);
		return wrapRequest(converter, oData);
	}

	private <O1 extends O, T extends M, D extends M, OD extends O> CompletableFuture<T>
			wrapRRequest(final IResponseConverter<O1, D, T> rConverter, final D data, final OD oData) {
		final CompletionStage<D> data2 = CompletableFuture.completedFuture(data);
		return mOriginal.request(rConverter.getTypeA(), oData).thenCombine(data2, rConverter);
	}

	private <O1 extends O, T extends M, OD extends O> CompletableFuture<T>
			wrapRequest(final IConverter<O1, T> converter, final OD oData) {
		return mOriginal.request(converter.getTypeA(), oData).thenApply(converter);
	}

	@Override
	public IInteractiveQueue<Object> common() {
		return mOriginal.common();
	}

	@Override
	public <T> CompletableFuture<T> newFuture() {
		return mOriginal.newFuture();
	}
}
