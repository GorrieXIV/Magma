figure;

file = getenv('BENCH_INPUT');
data = importdata(file);

new_data = [];
m = 1;
for row = (1 : length(data))
  val = data(row, :);
  m = val(1);
  new_data = [new_data ; val];
end;

new_data = [new_data ; [m + 1, val(2 : size(new_data, 2))]];

x_axis = new_data(:, 1);
[sx1, sy1] = stairs(x_axis, new_data(:, 2));
[sx1, sy2] = stairs(x_axis, new_data(:, 3));
[sx1, sy3] = stairs(x_axis, new_data(:, 4));
[sx1, sy4] = stairs(x_axis, new_data(:, 5));
plot(sx1, sy1, '-', sx1, sy2, ':', sx1, sy3, '-.c', sx1, sy4, '--');
axis([1, 21, 0, 8]);
legend('Total time', 'Discrete log time', 'SLP eval time', ...
       'SL2 oracle time', 'Location', 'NorthWest');

xlabel('m, q = 3^{2m + 1}');
ylabel('Average time');

fig = gcf;
file = getenv('BENCH_OUTPUT');
print(fig, '-deps2', file);
exit;
