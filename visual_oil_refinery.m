; Little visualization of the olp problem
; using modifiable Octave code

x = 0:0.1:10;
light = (59-12*x)/16;
middle = (12-x)/7;
heavy = (13-4*x)/2;
consumption = (205-25*x)/30;

plot(x, light, x, middle, x, heavy, x, consumption);
grid();
axis([0, 10, 0, 10], "equal");
xlabel("x1");
ylabel("x2");
