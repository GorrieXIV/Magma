% Quotients of mixing time with accelerator
data2 = importdata('mixing.cox.data');
data1 = importdata('mixing.coxcox.data');

quots1 = data1.data(:, 2) ./ data2.data(:, 2);

% Quotients of mixing time without accelerator
data2 = importdata('mixing.cox.nonacc.data');
data1 = importdata('mixing.coxcox.nonacc.data');

quots2 = data1.data(:, 2) ./ data2.data(:, 2);
idx = data1.data(:, 1);

% Obtain plot
plot(idx, quots1, '-', idx, quots2, '-.');
axis([1, 100, 0, 2.5]);
legend('Accelerator quotients', 'PR quotients');
xlabel('d');
ylabel('Mixing time quotient');

% Write an EPS
fig = gcf;
outfile = getenv('FIG_OUTPUT');
print(fig, '-deps2', outfile);
exit;
