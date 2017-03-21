#baseName <- "mixing_time"
mix <- read.table("mixing_time_normal.data", header = TRUE)
x11()

par(lab = c(20, 40, 0), type = "s", xaxs  = "i", yaxs= "i")
plot.new()
plot(mix$n, y = mix$mix, xlab = "d",
     ylab = "Mixing time", ylim = c(0, 350),
     xlim = c(1, 50), type = "l",
     col = "black", lty = 4)

# Add more data to plot
mix <- read.table("mixing_time_acc.data", header = TRUE)
points(mix$n, y = mix$mix, lty = 1, type = "l", col = "black")

# Add legend
legend(x = "topleft", legend = c("Normal PR", "With acc"),
       col = c("black", "black"), lty = c(4, 1))

dev.copy2eps(file = "mixing_time.bak.eps")
dev2bitmap(file = "mixing_time.png")
graphics.off()
