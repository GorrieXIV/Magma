figure;

file = getenv('BENCH_INPUT');
data = importdata(file);

new_data = [];
m = 1;
val = 0;
i = 0;
for row = (1 : length(data)),
  if data(row, 1) > m 
    new_data = [new_data ; m val / i];
    m = data(row, 1);
    val = data(row, 2);
    i = 1;
  else
    val = val + data(row, 2);
    i = i + 1;
  end;
end;

new_data = [new_data ; m, val / i]
new_data = [new_data ; m + 1, val / i]

x_axis = new_data(:, 1);
[sx1, sy1] = stairs(x_axis, new_data(:, 2));
plot(sx1, sy1, 'k');
axis([1, 21, 0, 90]);
%title('Benchmark of small Ree conjugation');

xlabel('m, q = 3^{2m + 1}');
ylabel('Average time');
%legend('Standard naming', 'Conjugate naming');

fig = gcf;
file = getenv('BENCH_OUTPUT');
print(fig, '-deps2', file);
exit;
