figure;

file = getenv('BENCH_INPUT');
data = importdata(file);

x_axis = data(:, 1);
[sx1, sy1] = stairs(x_axis, data(:, 2));
%[sx2, sy2] = stairs(x_axis, data(:, 3));
plot(sx1, sy1, 'k');
%plot(sx1, sy1, 'k:', sx2, sy2, 'k');
%axis([0, 86, 0, 10.5]);
axis([0, 100, 0, 3.1]);
axis tight;
title('Benchmark of Suzuki conjugation');

xlabel('m, where q = 2^{2m + 1}');
ylabel('Average time');
%legend('Total time', 'Discrete log time', 'Location', 'NorthWest');

bench_fig = gcf;
file = getenv('BENCH_OUTPUT');
print(bench_fig, '-deps2', file);
exit;

